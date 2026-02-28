#!/usr/bin/perl

# check inlet temp every minute, hddtemp every minute (ensuring
# doesn't spinup spundown disks), and sensors every few seconds, and
# adjust individual fans according to own threshold curves, overriding
# iDrac settings with fallback

# background information:
# https://www.dell.com/community/PowerEdge-Hardware-General/T130-Fan-Speed-Algorithm/td-p/5052692
# https://serverfault.com/questions/715387/how-do-i-stop-dell-r730xd-fans-from-going-full-speed-when-broadcom-qlogic-netxtr/733064#733064

use strict;
use warnings;
use List::MoreUtils qw( apply );
use File::Temp qw(tempfile);
use JSON::Parse qw/parse_json parse_json_safe/;
use Data::Dumper;
use POSIX ":sys_wait_h"; # for nonblocking read
use Time::HiRes qw (sleep);
use Cwd;
use Errno qw(EINTR);
use Fcntl qw(:DEFAULT :flock :seek :Fcompat);
use File::FcntlLock;

my $static_speed_low;
my $static_speed_high;   # This is the speed value at 100% demand
                         # ie what we consider the point we don't
                         # really want to get hotter but still
                         # tolerate
my ($ipmi_inlet_sensorname, $ipmi_exhaust_sensorname);

my $default_exhaust_threshold; # The exhaust temperature we use, set
                               # from above, which we fail back to
                               # letting the drac control the fans
my $base_temp;           # No fans when below this temp
my $desired_temp1;       # Aim to keep the temperature below this
my $desired_temp2;       # Really ramp up fans above this
my $desired_temp3;       # Really ramp up fans above this
my $demand1;             # Prescaled (not taking into effect static_speed_low/high) demand at temp1
my $demand2;             # Prescaled (not taking into effect static_speed_low/high) demand at temp2
my $demand3;             # Prescaled (not taking into effect static_speed_low/high) demand at temp3

my $in_deadband=0;       # if already in hysteresis deadband, then we
                         # adopt the hysteresis value.  Otherwise we
                         # servo down to the demandpoint, and then
                         # when we reach that, set $in_deadband
my $hysteresis;          # Don't ramp up velocity unless demand
                         # difference is greater than this.  Ramp
                         # down ASAP however, to bias quietness, and
                         # thus end up removing noise changes for
                         # just small changes in computing

my $fans;                # which fans are being controlled by this
                         # daemon?  0xff = all fans, 0 to 5 for
                         # individual fans

sub custom_temperature_calculation;

# Every 20 minutes (enough to establish spin-down), invalidate the
# cache of the slowly changing hdd temperatures to allow them to be
# refreshed
my $hdd_poll_interval=1200;
# Megasascli doesn't appear to wake drives or keep them spinning, and
# it's much quicker, so can afford to poll more often
my $megasascli_poll_interval=300;
# Raid controller is less expensive to poll, but also should't change
# overly rapidly (but it doesn't have a huge heatsink, so don't be too slow)
my $raid_controller_poll_interval=60;
# Every 60 seconds, invalidate the cache of the slowly changing
# ambient temperatures to allow them to be refreshed
my $ambient_poll_interval=60;
my $exhaust_poll_interval=60;
# And put fan back under our control once per minute if someone
# slipped it back into idrac mode, if all conditions are correct
my $manual_mode_reset_interval=60;
my $cpu_poll_interval=3;

my $sensors_ref;
my $temperature_calculation_sub;

my $lastfan;

my $quiet=0;          # whether to print stats at all
my $print_stats = 0;  # whether to print stats this run

my $tempfilename;     # just a generic tmpfile owned independently by each fork

my %tempfilename;     # the hash of tmpfiles we use to cache all results
my %tempfh;           # and handles

my $last_print_regular_stats=time; # when this thread last output regular stats

my @daemon_pids;      # pids for each of the children in turn
my @daemons;          # List of fans to supply to ipmitool - 0xff
                      # denotes all fans, and 0 to 5 would be each of
                      # the 6 individual fans, left to right, in a
                      # poweredge rackmounted server
my %children;
my $started;
my $signame;

my $FAILED=0;         # I'm too much of a shell scripter to not get confused as to whether a successful function should not return 0
my $SUCCEEDED=1;

sub print_usage {
  print STDERR <<EOF;
Usage: $0 [-q] [-f <conf_file>]
Controls poweredge (or any other type of server, really) fans dynamically

  -q                   Quiet - only print stats when necessary instead of every minute
  -f                   Supply conffile (/etc/poweredge-fand.conf default)
  -h|--help            Display this help and exit
EOF
  exit 1;
}

my %included_conf_file;
sub include {
  # http://www.perlmonks.org/?node_id=393426 but a bit different to
  # the version you can see there now in 2025, or maybe this was the
  # version I found that works when you're not trying to write a
  # module...?  Their code wants &include to be defined as
  # &module::include, and circa 2025, I was now seeing scope issues
  # without that, but removed `package DB; # causes eval to evaluate
  # the string in the caller's scope` and the code started to work
  # again.  So let's go with that...
  my ($filename) = @_;

  my $code;
  {
    open my $fh, '<', $filename or die "Cannot open $filename: $!";
    local $/; # Temporarily undefine the input record separator
    $code = <$fh>;
    close $fh;
  }

  $code = qq[#line 1 "$filename"\n] .
    $code;
  #  print "evaling code: $code\n";
  my $success=$SUCCEEDED;
  if (!defined $included_conf_file{$filename}
      or $included_conf_file{$filename} ne $code) {
    if (!defined $fans) {
      print "Parsing file $filename\n";
    } else {
      print "fan$fans: re-parsing file $filename\n";
    }
    $success = eval $code;
    $included_conf_file{$filename} = $code;
  }
  if (!$success) {
    die "Can't eval '$filename': $@";
    # FIXME: warn?
  }
  #  print "done...\n";
}

# to get reentrant signal handler, we set a flag.  To be as responsive
# as possible to that flag, check before and after every time we
# deliberately sleep as part of a loop
sub sleep_and_check_for_exit {
  my (@args) = (@_);

  if ($signame) {
    exit;
  }
  sleep @args;
  if ($signame) {
    exit;
  }
}

# Only test true in one of the daemons, for the first fan (or the
# daemon that's controlling all fans simultaneously)
sub perform_only_once {
  return (!defined $fans or $fans == 0 or $fans == 0xff);
}

# Only print out the stats in one of the daemons, for the first
# fan (or the daemon that's controlling all fans simultaneously)
sub print_stats_once {
  my $res=($print_stats and
    perform_only_once());
  return $res;
}

sub is_num {
  my ($val) = @_;
  if ( $val =~ /^[-+]?(\d*\.?\d+|\d+\.?\d*)+$/ ) {
    return $SUCCEEDED;
  }
  print "fan$fans: is_num($val)=0\n"; # should probably warn about failures to parse values, but if you don't care about a particular error, perhaps add this clause: if !$quiet;
  return $FAILED;
}

# returns undef if there are no inputs, and ignores inputs that are
# undef
sub average {
  my (@v) = (@_);

  my $div = 0;
  my $tot = 0;
  foreach my $v (@v) {
    if (defined $v && is_num($v)) {
      $tot += $v;
      $div++;
    }
  }
  my $avg=undef;
  if ($div > 0) {
    $avg = sprintf "%.2f", $tot/$div;
  }
  return $avg;
}

# a way to add an offset that doesn't baulk on the value being
# undefined, without complicating syntax
sub offset {
  my ($v, $offset) = (@_);
  if ((defined $v) && is_num($v)) {
    return $v+$offset;
  } else {
    return undef;
  }
}

# calculates the weighted averages
# (i,a, j,b, k,c, ....) as
# i*a, j*b, k*c etc, where i,j,k etc are integers>=1
# It still handles ignoring elements that are null
sub weighted_average {
  my (@v) = (@_);

  my (@vp) = ();

  foreach (my $i=0; $i<@v; $i+=2) {
    my $integer_weight=$v[$i];
    my $value=$v[$i+1];
    foreach (my $j=0; $j<$integer_weight; $j++) {
      push @vp, $value;
    }
  }
  my $a = average(@vp);
  # print "weighted average @v -> @vp -> $a\n";
  return $a;
}

# returns undef if there are no inputs, and ignores inputs that are
# undef
sub max {
  my (@v) = (@_);
  my $max=undef;
  foreach my $v (@v) {
    if ((defined $v) && is_num($v)) {
      if (!defined $max or $v > $max) {
        $max = $v;
      }
    }
  }
  return $max;
}

my %hdd_cache_temp;
my %hdd_cache_time;
sub hddtemp {
  my ($device)=(@_);

  # if /usr/local/bin/megaclisas-status exists, then parse it for
  # hddtemps, and if user supplies a parameter of the form of [32:13],
  # interpret it as "Slot ID".  Otherwise we have to parse hddtemp,
  # and for that, we don't know how many lockfiles we're going to have
  # to arrange, so we can't make use of obtain_cachable()
  if (-x "/usr/local/bin/megaclisas-status") {
    my @drive_temps = obtain_cachable
      ("megaclisas_temp",
       $megasascli_poll_interval,
       "timeout -k 1 30 /usr/local/bin/megaclisas-status");

    # if not [*:*]: (ie, if a device file)
    if (!($device =~ /^\[\d+:\d+\]$/)) {
      $device = Cwd::realpath (glob($device));
    }
    foreach my $megasas_line (@drive_temps) {
      my (@fields) =
        split(" ", $megasas_line);

      if (@fields and
          $fields[0] =~ /^c.....$/) {
        my $temp = $fields[-7];
        $temp =~ s/C$//; # get rid of the "C" celcius unit
        if ($device =~ /^\[\d+:\d+\]$/) {
          # the 5th last non-space field (including "|"), regardless
          # of how many spaces are in the drive model, is always the
          # slot id.
          my $scan_slot_id = $fields[-5];
          if ($scan_slot_id eq $device) {
            return $temp;
          }
        } else {
          my $scan_device = $fields[-1];
          if ($scan_device eq $device) {
            return $temp;
          }
        }
      }
    }
    # if we haven't returned by now, then the device didn't appear in
    # megaclisas output.  Fall back to old fashioned hddtemp
  }

  # At this point, if we were provided [*:*] style device names, we
  # didn't obtain the temperature from megasas, and we can't go any
  # further.
  return undef if ! -e $device;

  # But with a device name, we could fallback to hddtemp
  if (!defined $hdd_cache_time{$device} or
      $hdd_cache_time{$device} > $hdd_poll_interval) {
    # could just be a simple pipe, but hddtemp has a strong posibility
    # to be stuck in a D state, and hold STDERR open despite a kill
    # -9, so instead just send it to a tempfile, and read from that
    # tempfile

    # Some HDDs will be spun down, so they return "not available".
    # Treat them as if they weren't there.
    system("timeout -k 1 30 /usr/local/bin/hddtemp --no-device --numeric $device | grep -v 'not available' > $tempfilename");

    my $val = `cat < $tempfilename`; chomp $val;
    if ($val ne "") {
      $hdd_cache_temp{$device} = $val;
      $hdd_cache_time{$device} = time;
    }
  }

  return $hdd_cache_temp{$device};
}

sub lock {
  my ($fh, $name)=(@_);
  # We have to use fcntl() rather than the easier to use flock,
  # because the filedescriptors come from our parent, and all users of
  # the same file descriptor share the same flock locks.  If this
  # didn't work, you'd simply revert back to flock, but get each child
  # to reopen the tempfile as a new filehandle only they have

  # Define the flock structure (l_type, l_whence, l_start, l_len, l_pid)
  # F_WRLCK: Exclusive Write Lock
  # SEEK_SET: Start from beginning
  # 0, 0: Offset 0, Length 0 means entire file regardless of how much it grows
  my $fs = new File::FcntlLock;
  $fs->l_type( F_WRLCK );
  $fs->l_whence( SEEK_SET );
  $fs->l_start( 0 );

  # Apply the lock (blocks until available)
  my $result;
  my $blocked;
  # print STDERR "fan$fans: ";
  while (1) {
    # print STDERR "trying to lock '$name'\n";
    $result = $fs->lock( $fh, F_SETLKW );
    if (!$result) {
      if ($! == EINTR) {
        # This thread gets SIGUSR1 once per minute from
        # wait_and_poll_output_handlers, which will interrupt us if
        # we're locked

        if ($blocked) {
          # if blocked for more than 1 minute, warn
          print STDERR "fan$fans: Still can't lock '$name': $fs->error\n";
        }
        $blocked=1;
        next;
      }
      # print STDERR "fan$fans: lock, result=$result, !=$!\n";
      die "Cannot lock file '$name': $fs->error";
    } else {
      last;
    }
  };
  if ($blocked) {
    # FIXME: should print this only if still blocked from prior minute?
    print STDERR "fan$fans: locked after blocking: '$name'\n";
  }
}

sub unlock {
  my ($fh, $name)=(@_);

  # reverse the lock
  my $fs = new File::FcntlLock;
  $fs->l_type(F_UNLCK);

  seek($fh, 0, SEEK_SET) or die "seek failed: '$name': $!";
  my $result;
  my $blocked;
  # print STDERR "fan$fans: ";
  while (1) {
    # print STDERR "trying to unlock '$name'\n";
    $result = $fs->lock( $fh, F_SETLK );
    if (!$result) {
      if ($! == EINTR) {
        # This thread gets SIGUSR1 once per minute from
        # wait_and_poll_output_handlers, which will interrupt us if
        # we're locked

        if ($blocked) {
          # if blocked for more than 1 minute, warn
          print STDERR "fan$fans: Still can't unlock '$name': $fs->error\n";
        }
        $blocked=1;
        next;
      }
      # print STDERR "fan$fans: unlock, result=$result, !=$!\n";
      die "Cannot unlock file '$name': $fs->error";
    } else {
      last;
    }
  };
  if ($blocked) {
    # FIXME: should print this only if still blocked from prior minute?
    print STDERR "fan$fans: unlocked after blocking: '$name'\n";
  }
}

# When we otherwise could just use a simple pipe, but we want to
# protect against something getting stuck in the D state, holding
# STDERR open despite a kill -9, we can instead just send it to a
# tempfile, and read from that tempfile.  We also then gain a
# mechanism to cache the output between all forks dealing with the
# different fans.
sub obtain_cachable {
  my ($cache_bucket, $cache_interval, $cmd) = (@_);

  my $cache_file=$tempfilename{$cache_bucket};
  my $cache_fh  =$tempfh      {$cache_bucket};

  # always go for an exclusive (write) lock, *then* compare if mtime
  # of that file has passed the cache_interval yet.  If not, we
  # quickly read the file and unlock.  If we had to block because
  # someone else was writing it, then we'll eventually be unblocked,
  # we'll determine the age of the file and find that it's fresh (or
  # in need of invalidation)

  lock($cache_fh, $cache_file);
  my ($mtime) = (stat($cache_file))[9];
  die "our state file has been deleted: $!" if (!defined $mtime);

  # if the file had previously been written but an error lead to
  # there being no content, or only just opened, then we force a new
  # generation of the output.  Otherwise, we generate the output
  # only if the cache_interval has expired
  if (!(-s $cache_file) or
      (time() - $mtime >= $cache_interval)) {
    # perlfunc: open(): "Duping filehandles"
    system("$cmd > $cache_file");
    # system("echo $cache_bucket 1>&2 ; grep -H . $cache_file 1>&2");
  }

  seek $cache_fh, 0, 0 or die "Cannot seek file '$cache_file' - $!";

  my (@res, $res);
  @res = <$cache_fh>;
  chomp @res;

  unlock($cache_fh, $cache_file);
  if (wantarray) {
    return @res;
  } else {
    $res = join "\n", @res;
    return $res;
  }
}

sub raid_controller_temp {
  my $val=obtain_cachable
    ("raid_controller_temp",
     $raid_controller_poll_interval,
     "timeout -k 1 30 /opt/MegaRAID/MegaCli/MegaCli64 -AdpAllInfo -aALL -NoLog | grep -i ^ROC.temperature | awk '{print \$4}'");
  return $val;
}

sub raid_controller_battery_temp {
  my $val=obtain_cachable
    ("raid_controller_battery_temp",
     $raid_controller_poll_interval,
     "timeout -k 1 30 /opt/MegaRAID/MegaCli/MegaCli64 -AdpBbuCmd -GetBbuStatus -aALL -NoLog | grep -i ^temperature | awk '{print \$2}'");
  return $val;
}

my $ambient_cache_temp = 20;
sub ambient_temp {
  my @ambient_ipmitemps = obtain_cachable
    ("ambient_temp",
     $ambient_poll_interval,
    "timeout -k 1 30 ipmitool sdr type temperature | grep '$ipmi_inlet_sensorname' | grep [0-9]");

  # apply from List::MoreUtils
  @ambient_ipmitemps = apply { s/.*\| ([^ ]*) degrees C.*/$1/ } @ambient_ipmitemps;

  if (@ambient_ipmitemps) {
    # ipmitool often fails - just keep using the previous result til
    # it succeeds
    $ambient_cache_temp = average(@ambient_ipmitemps);
  }

  return $ambient_cache_temp;
}

my $exhaust_cache_temp = 30;
sub exhaust_temp {
  my @exhaust_ipmitemps = obtain_cachable
    ("exhaust_temp",
     $exhaust_poll_interval,
     "timeout -k 1 30 ipmitool sdr type temperature | grep '$ipmi_exhaust_sensorname' | grep [0-9]");

  # apply from List::MoreUtils
  @exhaust_ipmitemps = apply { s/.*\| ([^ ]*) degrees C.*/$1/ } @exhaust_ipmitemps;

  if (@exhaust_ipmitemps) {
    # ipmitool often fails - just keep using the previous result til
    # it succeeds
    $exhaust_cache_temp = average(@exhaust_ipmitemps);
  }

  return $exhaust_cache_temp;
}

sub set_fans_mode {
  my ($new_mode) = (@_);
  my $return=$SUCCEEDED;

  # All fan controllers have to agree to take the fan control out of
  # idrac control (or, more correctly, any of the controllers can put
  # it back into auto-mode), so the first child that wants to change
  # the mode has to take a lock, check a statefile, determine whether
  # we're flipping states, perform the state change itself, updating a
  # statefile and unlock (the reset is done once per minute anyway if
  # someone did slip it back into idrac control, but then didn't have
  # the authority to move it back under manual control)
  my $fh=$tempfh{idrac_control};
  my $file=$tempfilename{idrac_control};
  lock($fh,$file);
  seek $fh, 0, 0 or die "Cannot seek file '$file' - $!";

  my ($prev_mode) = <$fh>;
  $prev_mode="" if !defined $prev_mode;
  chomp $prev_mode;
  my $print_info=0;
  my $will_run_mode_switch=0;
  if ($new_mode eq "default") {
    # this is an abnormal condition, so always warn about it, even in
    # quiet mode
    $print_info=1;
  }
  if (($new_mode eq "reset") or ($new_mode ne $prev_mode)) {
    $will_run_mode_switch=1;
    if ($new_mode ne "reset") {
      seek $fh, 0, 0 or die "Cannot seek file '$file' - $!";
      print $fh "$new_mode\n";
    }
    # if regularly printing stats, or changing mode, then print the
    # new mode
    if ($print_stats or
        ($new_mode ne "reset")) {
      $print_info=1;
    }
    if ($new_mode eq "reset") {
      $new_mode=$prev_mode;
    }
  }

  if ($print_info) {
    my $header = defined $fans ? "fan$fans" : "parent";
    if ($new_mode eq "servo") {
      print "$header: $prev_mode->$new_mode    --> enable our manual fan control\n";
    } else {
      print "$header: $prev_mode->$new_mode    --> enable dynamic (idrac automatic) fan control\n";
    }
  } else {
    print "\n" if $print_stats;  # in the servo case, the caller
                                 # before us didn't print a newline so
                                 # we could append to it, but it turns
                                 # out we're not printing anything
  }

  if ($will_run_mode_switch) {
    if ($new_mode eq "servo") {
      # ipmitool routinely fails; that's OK, if this fails, want to
      # return telling caller not to think we've made a change
      if (system("ipmitool raw 0x30 0x30 0x01 0x00") != 0) {
        $return=$FAILED;
        goto set_fans_mode_final;
      }
    } else {
      foreach my $attempt (1..10) {
        # ipmitool routinely fails, so try up to 10 times since we are
        # already the failure path, so need to be reliable ourselves
        if (system("ipmitool raw 0x30 0x30 0x01 0x01") == 0) {
          $return=$SUCCEEDED;
          goto set_fans_mode_final;
        }
        sleep_and_check_for_exit 1;
        print "  Retrying dynamic control $attempt\n";
      }
      print "Retries of dynamic control all failed\n";
      $return=$FAILED;
      goto set_fans_mode_final;
    }
    $return=$SUCCEEDED;
    goto set_fans_mode_final;
  }

 set_fans_mode_final:
  unlock($fh,$file);
  return $return;
}

sub set_fans_default {
  $lastfan=undef;
  return set_fans_mode "default";
}

sub set_fans_servo {
  my $weighted_temp = custom_temperature_calculation();

  if ((!defined $weighted_temp) or ($weighted_temp == 0)) {
    print "fan$fans: Error reading all temperatures! Fallback to idrac control\n";
    set_fans_default();
    return $FAILED;  # we always failed, even if set_fans_default succeeded.
                     # set_fans_default is an exceptional condition
  }
  my $ambient_temp = ambient_temp();
  my $exhaust_temp = exhaust_temp();
  print "ambient_temp $ambient_temp ; exhaust_temp $exhaust_temp" if print_stats_once;

  if (!set_fans_mode "servo") {
    return $FAILED;
  }
  my $demand = 0; # sort of starts off with a range roughly 0-255,
                  # which we multiply later to be ranged roughly
                  # between 0-100% of
                  # ($static_speed_low - $static_speed_high)
  if (($weighted_temp > $base_temp) and
      ($weighted_temp < $desired_temp1)) {
    # slope m = (y2-y1)/(x2-x1)
    # y - y1 = (x-x1)(y2-y1)/(x2-x1)
    # y1 = 0 ; x1 = base_temp ; y2 = demand1 ; x2 = desired_temp1
    # x = weighted_temp
    $demand = 0        + ($weighted_temp - $base_temp    ) * ($demand1 - 0       )/($desired_temp1 - $base_temp    );
  } elsif (($weighted_temp >= $desired_temp1) and
           ($weighted_temp < $desired_temp2)) {
    # y1 = demand1 ; x1 = desired_temp1 ; y2 = demand2 ; x2 = desired_temp2
    $demand = $demand1 + ($weighted_temp - $desired_temp1) * ($demand2 - $demand1)/($desired_temp2 - $desired_temp1);
  } elsif ($weighted_temp >= $desired_temp2) {
    # y1 = demand2 ; x1 = desired_temp2 ; y2 = demand3 ; x2 = desired_temp3
    # demand will increase above $demand3 for temps above $desired_temp3, linearly, until we cap it below
    $demand = $demand2 + ($weighted_temp - $desired_temp2) * ($demand3 - $demand2)/($desired_temp3 - $desired_temp2);
  } else {
    # the only possibility left is $weighted_temp < $base_temp
    # which we've already decided is demand=0
  }

  my $demand_out = int($static_speed_low + $demand/100*($static_speed_high-$static_speed_low));
  if ($demand_out>100) {
    $demand_out=100; # top value accepted by ipmitool raw 0x30 ... is
                     # 0x64.  Which is strangely enough, 100.
  }
  my $stats_to_print=sprintf "weighted_temp($fans) = %6.2f ; demand($fans)=%6.2f -> %3i", $weighted_temp, $demand, $demand_out;
  $demand = sprintf("%i", $demand_out);
  # print "demand = $demand\n";

  # ramp down the fans quickly upon lack of demand, don't ramp them
  # up/down to tiny spikes of 1 fan unit.
  if ($in_deadband) {
    $in_deadband = ((defined $lastfan) and
                    ($demand > $lastfan - $hysteresis) and
                    ($demand < $lastfan + $hysteresis));
  } else {
    $in_deadband = ((defined $lastfan) and
                    ($demand == $lastfan));
  }
  my $demand_has_changed = ((! defined $lastfan) ||
                            (! $in_deadband)     ||
                            ($demand == 0) || ($demand == 100));
  if ($print_stats or
      $demand_has_changed) {
    # allowed to print out of minute-printing cycle if the demand
    # actually changes
    print "$stats_to_print --> ipmitool raw 0x30 0x30 0x02 $fans " . ( $demand_has_changed and defined $lastfan ? "$lastfan->" : "" ) . "$demand\n";
    # ipmitool routinely fails; that's OK, if this fails, want to
    # return telling caller not to think we've made a change
    if ($demand_has_changed) {
      if (system("ipmitool raw 0x30 0x30 0x02 $fans $demand") != 0) {
        return $FAILED;
      }
      $lastfan = $demand;
      if ((!defined $lastfan) or ($demand > $lastfan)) {
        $in_deadband = 1;  # allow rapid sustained decrease, but
                           # resist going back up again
      }
    }
  }
  return $SUCCEEDED;
}

sub wait_and_poll_output_handlers {
  while (1) {
    # check to see whether any children have died yet, and exit the
    # loop as soon as one has
    my $pid = waitpid(-1, WNOHANG);
    if ($pid > 0) {
      delete $children{$pid};
      return;
    }

    my $inter_process_sequencing_sleep_interval = 10;
    my $already_slept=0;
    # tell all children to output their stats
    foreach my $pid (@daemon_pids) {
      # print STDERR "Signalling child: $pid\n";
      kill "USR1", $pid;
      # After the first child is triggered, allow them a lot of time
      # to work their way through the expensive checks.  Hopefully
      # they are finished by the time the second come through, and
      # subsequent children should all be able to access the cached
      # results, so allow them to cycle through quickly.  This should
      # allow the output to be mostly sorted correctly, but lockfiles
      # still protect the individual caches.
      sleep_and_check_for_exit $inter_process_sequencing_sleep_interval;
      $already_slept        += $inter_process_sequencing_sleep_interval;
      $inter_process_sequencing_sleep_interval = 1;
    }

    # every minute ($manual_mode_reset_interval seconds), iterate
    # through all the children and tell them to output, trying to keep
    # their output in rough order (keeping in mind they're
    # unsynchronised and subject to blocking conditions)
    sleep_and_check_for_exit ($manual_mode_reset_interval -
                              $already_slept);
  }
}

my $parent_pid=$$;

sub we_are_parent {
  return ($$ == $parent_pid);
}

# from man perlipc
sub child_handler {
  # don't change $! and $? outside handler
  local ($!, $?);
  while ( (my $pid = waitpid(-1, WNOHANG)) > 0 ) {
    delete $children{$pid};
    # cleanup_child($pid, $?);
  }
};

# It'd be lovely if our regular updates (and to a lesser extent, our
# updates when actively changing the fan) were ordered.  We could do
# this when we're running separate daemons for each fan, by triggering
# this from a signal handler and signalling each in sequence, waiting
# for it to do the write (so waiting roughly 3 seconds per fan).  It
# won't always be correct, but it should be close enough that the
# output isn't discombobulating.
sub reset_stats_handler {
  # we force an update regardless of how many seconds since last
  # output by this thread
  # print STDERR "fan$fans: resetting last_print_regular_stats=$last_print_regular_stats to 0\n";
  $last_print_regular_stats = 0;
}

sub signal_handler {
  $signame = shift;
  print STDERR "poweredge-fand(" . (we_are_parent() ? "" : "$parent_pid -> " ) . "$$): Recieved signal $signame\n";
  exit;
};
END {
  # handler for internal errors (floating point, die, etc) that don't
  # cause signals
  my $exit = $?;
  if (we_are_parent()) {
    if ($started) {
      # we're the parent, and need to kill all our children and reset
      # fans back to default
      foreach my $cache_bucket (keys %tempfilename) {
        my $cache_file=$tempfilename{$cache_bucket};
        print STDERR "Unlinking tmpfile(parent) '$cache_file'\n";
        unlink $cache_file;
      }

      # sleep 0.5;  # systemd has probably already sent signals to all
                  # the children, who are now busily deleting their
                  # tmpfiles with signal handler disengaged.  Give
                  # them a chance to run before killing them
      my (@children) = keys %children;
      print STDERR "Killing children: @children\n";
      kill "TERM", @children;
      my $children_left;
      foreach my $checks (1..100) {
        if ( (my $pid = waitpid(-1, WNOHANG)) > 0) {
          delete $children{$pid};
          (@children) = keys %children;
        }
        $children_left = kill 0, @children;
        if ($children_left) {
          print STDERR "Of @children, we're still waiting for $children_left children to die\n"
        } else {
          last;
        }
        sleep 0.03;   # We try 100 times, or for at least 3 seconds
      }
      if ($children_left) {
        print STDERR "Some of @children may have not died. $children_left children were left\n"
      }
      print STDERR "Resetting fans back to default\n";
      my $saved_signame=$signame;
      $signame=undef;
      set_fans_default;
      $signame=$saved_signame;
    }
  } else {
    # we're a child daemon, and need to unlink our fork's temporary file
    print STDERR "Unlinking tmpfile(fan$fans) '$tempfilename'\n";
    unlink $tempfilename if defined $tempfilename;
    print STDERR "Child fan $fans dying: $$\n";
  }
  if ($signame) {
    $SIG{$signame} = "DEFAULT";
    kill $signame, $$;
    exit 130;  # fallback since seems to be ignoring SIGINT
  } else {
    $? = $exit;
  }
}

my $conf_file="/etc/poweredge-fand.conf";

while (@ARGV > 0) {
  if ($ARGV[0] eq "-q") {
    $quiet=1;
    $print_stats=0;
  } elsif ($ARGV[0] eq "-f") {
    $conf_file=$ARGV[1];
    shift @ARGV;
  } else {
    print_usage;
  }
  shift @ARGV;
}

include $conf_file;
$started=1;
$SIG{TERM} = $SIG{HUP} = $SIG{INT} = \&signal_handler;
$SIG{USR1} = \&reset_stats_handler;

foreach my $cache_bucket ("idrac_control", "sensors", "megaclisas_temp", "raid_controller_temp", "raid_controller_battery_temp", "ambient_temp", "exhaust_temp") {

  ($tempfh{$cache_bucket}, $tempfilename{$cache_bucket}) =
    tempfile("poweredge-fand.$cache_bucket.XXXXX", TMPDIR => 1);

  select $tempfh{$cache_bucket}; $| = 1;  # make unbuffered
}
select STDOUT; $| = 1;  # make unbuffered

foreach my $loop_fan (@daemons) {
  my $pid;
  if ($pid=fork) {
    #parent;
    $children{$pid}=1;
    push @daemon_pids, $pid;
    # keep looping
  } elsif ($pid==0) {
    #child;
    $fans=$loop_fan;
    print "Forked child $parent_pid -> $$ for fan $fans\n";
    last;
  } else {
    die "could not fork: #!";
  }
}

# if we are the parent, wait for the first child to die, then kill all
# our children (or just delegate the killing to systemd?)
if (we_are_parent()) {
  $SIG{CHLD} = \&child_handler;
  # wait for the first child to die, then exit, killing all the rest
  # (to signal to systemd that we died)
  wait_and_poll_output_handlers();

  my $exit = $? >> 8;
  print "One of our children died with $exit, so we're exiting as a group\n";
  exit $exit;
}

my $tempfh;
($tempfh, $tempfilename) = tempfile("poweredge-fand.child-$fans.XXXXX", TMPDIR => 1);

while () {
  # Let's parse the file everytime, and detect changes, so we can
  # quickly debug new curves without waiting for the restart sequence:
  include $conf_file;

  my $sensors_json = obtain_cachable
    ("sensors",
     $cpu_poll_interval,
     "timeout -k 1 30 sensors -j 2>/dev/null");  # discard errors, annoyingly, but we do need to suppress things like
                                                 # "ERROR: Can't get value of subfeature fan1_input: Can't read"

  if (!($sensors_ref = parse_json_safe $sensors_json)) {
    $sensors_json =~ s/\n/\\n/g;
    $sensors_json =  substr($sensors_json, 0, 80);
    print STDERR "fan$fans: discarding sensors from this run: '$sensors_ref' extracted from '$sensors_json...'\n";
    goto nextpoll;
  };

  # my $ambient_temp = ambient_temp();
  # if ($ambient_temp > $default_threshold) {
  my $exhaust_temp = exhaust_temp();
  if ($exhaust_temp > $default_exhaust_threshold) {
    if (perform_only_once) {
      #print "fallback because of high ambient temperature $ambient_temp > $default_threshold\n";
      print "fan$fans: fallback because of high exhaust temperature $exhaust_temp > $default_exhaust_threshold\n";
    }
    if (!set_fans_default()) {
      # return for next loop without resetting timers and delta change
      # if that fails
      goto nextpoll;
    }
  } else {
    if (!set_fans_servo()) {
      # return for next loop without resetting timers and delta change
      # if that fails
      goto nextpoll;
    }
  }

  $print_stats = 0;
  # print "fan$fans: is time - $last_print_regular_stats > $manual_mode_reset_interval?\n";
  if (time - $last_print_regular_stats >
      ($manual_mode_reset_interval + 60)) {
    # Hopefully we're told by our parents when to reset the loop, but
    # have a fallback if they forget to trigger us a minute past-due.
    if (perform_only_once) {
      set_fans_mode "reset"; # just in case the RAC has rebooted, it
                             # will go back into default control, so
                             # make sure we set it appropriately once
                             # per minute
    }
    $last_print_regular_stats=time;
    $print_stats = 1 if !$quiet;
  }
 nextpoll:
  sleep_and_check_for_exit $cpu_poll_interval;
}
