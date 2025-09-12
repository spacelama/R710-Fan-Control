#!/usr/bin/perl

# check inlet temp every minute, hddtemp every minute (ensuring
# doesn't spinup spundown disks), and sensors every few seconds, and
# adjust individual fans according to own threshold curves, overriding
# iDrac settings with fallback

# background information:
# https://www.dell.com/community/PowerEdge-Hardware-General/T130-Fan-Speed-Algorithm/td-p/5052692
# https://serverfault.com/questions/715387/how-do-i-stop-dell-r730xd-fans-from-going-full-speed-when-broadcom-qlogic-netxtr/733064#733064
# could monitor H710 temperature with sudo env /opt/MegaRAID/MegaCli/MegaCli64 -AdpAllInfo -aALL | grep -i temperature

use strict;
use warnings;
use List::MoreUtils qw( apply );
use File::Temp qw(tempfile);
use JSON;
use Data::Dumper;
use POSIX ":sys_wait_h"; # for nonblocking read
use Time::HiRes qw (sleep);

my $static_speed_low;
my $static_speed_high;   # this is the speed value at 100% demand
                         # ie what we consider the point we don't
                         # really want to get hotter but still
                         # tolerate
my ($ipmi_inlet_sensorname, $ipmi_exhaust_sensorname);

my $default_exhaust_threshold; # the exhaust temperature we use above
                               # which we fail back to letting the drac
                               # control the fans
my $base_temp;           # no fans when below this temp
my $desired_temp1;       # aim to keep the temperature below this
my $desired_temp2;       # really ramp up fans above this
my $desired_temp3;       # really ramp up fans above this
my $demand1;             # prescaled (not taking into effect static_speed_low/high) demand at temp1
my $demand2;             # prescaled (not taking into effect static_speed_low/high) demand at temp2
my $demand3;             # prescaled (not taking into effect static_speed_low/high) demand at temp3

my $hysteresis;          # don't ramp up velocity unless demand
                         # difference is greater than this.  Ramp
                         # down ASAP however, to bias quietness, and
                         # thus end up removing noise changes for
                         # just small changes in computing

my $fans;                # which fans are being controlled by this daemon?  0xff = all fans,
                         # 0x00 to 0x05 for individual fans

sub custom_temperature_calculation;

# every 20 minutes (enough to establish spin-down), invalidate the
# cache of the slowly changing hdd temperatures to allow them to be
# refreshed
my $hdd_poll_interval=1200;
# raid controller is less expensive to poll, and should't change
# overly rapidly
my $raid_controller_poll_interval=30;
# every 60 seconds, invalidate the cache of the slowly changing
# ambient temperatures to allow them to be refreshed
my $ambient_poll_interval=60;
my $exhaust_poll_interval=60;
my $cpu_poll_interval=3;

my $sensors_ref;
my $temperature_calculation_sub;

my $current_mode;
my $lastfan;

my $quiet=0;          # whether to print stats at all
my $print_stats = 1;  # whether to print stats this run

my $tempfilename;
my @daemons;
my %children;
my $started;
my $signame;

sub print_usage {
  print STDERR "Usage: poweredge-fand.pl [-q] [-f <conf_file>]\n";
  exit 1;
}

sub include {
  # http://www.perlmonks.org/?node_id=393426
  #package DB;     # causes eval to evaluate the string in the caller's
  # scope.  Sometimes perl can be truly horrendous
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
  eval $code;
  if ("$@" ne "") {
    die "Can't eval $filename: $@";
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

# Only print out the stats in one of the daemons, for the first
# fan (or the daemon that's controlling all fans simultaneously)
sub print_stats_once {
  return $print_stats and
    ($fans == 0 or $fans == 0xff);
}

sub is_num {
  my ($val) = @_;
  if ( $val =~ /^[-+]?(\d*\.?\d+|\d+\.?\d*)+$/ ) {
    return 1;
  }
  print "is_num($val)=0\n"; # should probably warn about failures to parse values, but if you don't care about a particular error, perhaps add this clause: if !$quiet;
  return 0;
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

# calculates the weighted averages
# (i,a, j,b, k,c, ....) as
# i*a, j*b, k*c etc, where i,j,k etc are integers>=1
# It still handles ignoring elements that are null
sub weighted_average {
  my (@v) = (@_);

  my (@vp) = ();

  for (my $i=0; $i<@v; $i+=2) {
    my $integer_weight=$v[$i];
    my $value=$v[$i+1];
    for (my $j=0; $j<$integer_weight; $j++) {
      push @vp, $value;
    }
  }
  return average(@vp);
}

# returns undef if there are no inputs, and ignores inputs that are
# undef
sub max {
  my (@v) = (@_);
  my $max=undef;
  foreach my $v (@v) {
    if (defined $v) {
      if (!defined $max or $v > $max) {
        $max = $v;
      }
    }
  }
  return $max;
}

my %hdd_cache_temp;
my %hdd_cache_time;
# FIXME: should we use /usr/local/bin/megaclisas-status for all temps?  How does it handle drives in sleep mode?
sub hddtemp {
  my ($device)=(@_);

  # FIXME: if user supplies a parameter of the form of [32:13], interpret it as "Slot ID" form output by megaclisas-status
  return if ! -e $device;

  if (!defined $hdd_cache_time{$device} or
      $hdd_cache_time{$device} > $hdd_poll_interval) {
    # could just be a simple pipe, but hddtemp has a strong posibility
    # to be stuck in a D state, and hold STDERR open despite a kill
    # -9, so instead just send it to a tempfile, and read from that tempfile

    # Some HDDs will be spun down, so they return "not available".
    # Treat them as if they weren't there.
    system("timeout -k 1 20 /usr/local/bin/hddtemp --no-device --numeric $device | grep -v 'not available' > $tempfilename");

    my $val = `cat < $tempfilename`; chomp $val;
    if ($val ne "") {
      $hdd_cache_temp{$device} = $val;
      $hdd_cache_time{$device} = time;
    }
  }

  return $hdd_cache_temp{$device};
}

my $raid_controller_cache_temp;
my $raid_controller_cache_time;
sub raid_controller_temp {
  if (!defined $raid_controller_cache_time or
      $raid_controller_cache_time > $raid_controller_poll_interval) {
    # could just be a simple pipe, but protect against something
    # getting stuck in the D state, holding STDERR open despite a kill
    # -9, so instead just send it to a tempfile, and read from that
    # tempfile
    system("timeout -k 1 20 /opt/MegaRAID/MegaCli/MegaCli64 -AdpAllInfo -aALL | grep -i ^ROC.temperature | awk '{print \$4}' > $tempfilename");

    my $val = `cat < $tempfilename`; chomp $val;
    if ($val ne "") {
      $raid_controller_cache_temp = $val;
      $raid_controller_cache_time = time;
    }
  }

  return $raid_controller_cache_temp;
}

my $ambient_cache_temp = 20;
my $ambient_cache_time;
sub ambient_temp {
  if (!defined $ambient_cache_time or
      $ambient_cache_time > $ambient_poll_interval) {
    system("timeout -k 1 20 ipmitool sdr type temperature | grep '$ipmi_inlet_sensorname' | grep [0-9] > $tempfilename");

    my @ambient_ipmitemps = `cat < $tempfilename`;
    # apply from List::MoreUtils
    @ambient_ipmitemps = apply { s/.*\| ([^ ]*) degrees C.*/$1/ } @ambient_ipmitemps;

    if (@ambient_ipmitemps) {
      # ipmitool often fails - just keep using the previous result til
      # it succeeds
      $ambient_cache_temp = average(@ambient_ipmitemps);
      $ambient_cache_time = time;
    }
  }

  return $ambient_cache_temp;
}

my $exhaust_cache_temp = 30;
my $exhaust_cache_time;
sub exhaust_temp {
  if (!defined $exhaust_cache_time or
      $exhaust_cache_time > $exhaust_poll_interval) {
    system("timeout -k 1 20 ipmitool sdr type temperature | grep '$ipmi_exhaust_sensorname' | grep [0-9] > $tempfilename");

    my @exhaust_ipmitemps = `cat < $tempfilename`;
    # apply from List::MoreUtils
    @exhaust_ipmitemps = apply { s/.*\| ([^ ]*) degrees C.*/$1/ } @exhaust_ipmitemps;

    if (@exhaust_ipmitemps) {
      # ipmitool often fails - just keep using the previous result til
      # it succeeds
      $exhaust_cache_temp = average(@exhaust_ipmitemps);
      $exhaust_cache_time = time;
    }
  }

  return $exhaust_cache_temp;
}

sub set_fans_default {
  if (!defined $current_mode or $current_mode ne "default") {
    $current_mode="default";
    $lastfan=undef;
    # this is an abnormal condition, so always warn about it, even in
    # quiet mode
    print "--> enable dynamic (idrac automatic) fan control\n";
    foreach my $attempt (1..10) {
      # ipmitool routinely fails, so try up to 10 times since we are
      # already the failure path, so need to be reliable ourselves
      if (system("ipmitool raw 0x30 0x30 0x01 0x01") == 0) {
        return 1;
      }
      sleep_and_check_for_exit 1;
      print "  Retrying dynamic control $attempt\n";
    }
    print "Retries of dynamic control all failed\n";
    return 0;
  }
  return 1;
}

sub set_fans_servo {
  my $weighted_temp = custom_temperature_calculation();

  if ((!defined $weighted_temp) or ($weighted_temp == 0)) {
    print "Error reading all temperatures! Fallback to idrac control\n";
    set_fans_default();
    return 0;  # we always failed, even if set_fans_default succeeded
  }
  # my $ambient_temp = ambient_temp();
  # print "weighted_temp($fans) = $weighted_temp ; ambient_temp $ambient_temp\n" if $print_stats;
  my $exhaust_temp = exhaust_temp();
  print "weighted_temp($fans) = $weighted_temp ; exhaust_temp $exhaust_temp\n" if $print_stats;

  # take us out of idrac dynamic control, setting to manual control
  if ((!defined $current_mode) or ($current_mode ne "set")) {
    print "--> disable dynamic fan control\n" if !($quiet and (defined $current_mode) and ($current_mode eq "reset"));
    # ipmitool routinely fails; that's OK, if this fails, want to
    # return telling caller not to think we've made a change
    if (system("ipmitool raw 0x30 0x30 0x01 0x00") != 0) {
      return 0;
    }
    $current_mode="set";
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
  printf "demand($fans, %0.2f)", $demand if $print_stats;
  $demand = int($static_speed_low + $demand/100*($static_speed_high-$static_speed_low));
  if ($demand>255) {
    $demand=255;
  }
  printf " -> %i\n", $demand if $print_stats;
  # ramp down the fans quickly upon lack of demand, don't ramp them up
  # to tiny spikes of 1 fan unit.  FIXME: But should implement long
  # term smoothing of +/- 1 fan unit
  if (!defined $lastfan or
      $demand < $lastfan or
      $demand > $lastfan + $hysteresis) {
    $lastfan = $demand;
    $demand = sprintf("0x%x", $demand);
    # print "demand = $demand\n";
    print "--> ipmitool raw 0x30 0x30 0x02 $fans $demand\n";
    # ipmitool routinely fails; that's OK, if this fails, want to
    # return telling caller not to think we've made a change
    if (system("ipmitool raw 0x30 0x30 0x02 $fans $demand") != 0) {
      return 0;
    }
  }
  return 1;
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

sub signal_handler {
  $signame = shift;
  print "poweredge-fand(", (we_are_parent() ? "" : "$parent_pid -> " ), "$$): Recieved signal $signame\n";
  $SIG{$signame} = "DEFAULT";
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
      my (@children) = keys %children;
      print "Killing children: @children\n";
      kill "TERM", @children;
      my $children_left;
      for my $checks (1..100) {
        if ( (my $pid = waitpid(-1, WNOHANG)) > 0) {
          delete $children{$pid};
          (@children) = keys %children;
        }
        $children_left = kill 0, @children;
        if ($children_left) {
          print "Still waiting for $children_left children to die: @children\n"
        } else {
          last;
        }
        sleep 0.03
      }
      if ($children_left) {
        print "Not all children died. $children_left children were left, which may contain: @children\n"
      }
      print "Resetting fans back to default\n";
      my $saved_signame=$signame;
      $signame=undef;
      set_fans_default;
      $signame=$saved_signame;
    }
  } else {
    # we're a child daemon, and need to unlink our temporary file
    unlink $tempfilename if defined $tempfilename;
    print "Child fan $fans dying: $$\n";
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

include($conf_file);
$started=1;
$SIG{TERM} = $SIG{HUP} = $SIG{INT} = \&signal_handler;

foreach my $loop_fan (@daemons) {
  my $pid;
  if ($pid=fork) {
    #parent;
    $children{$pid}=1;
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
  wait;   # wait for the first child to die, then exit, killing all
          # the rest (to signal to systemd that we died)

  print "One of our children died with $?, so we're exiting\n";
  exit $?;
}

my $tempfh;
($tempfh, $tempfilename) = tempfile("poweredge-fand.temp.XXXXX", TMPDIR => 1);

my $last_print_stats=time;
while () {
  my $sensors_json = `timeout -k 1 20 sensors -j 2>/dev/null`;  # discard errors, annoyingly, but we do need to suppress things like
                                                                # "ERROR: Can't get value of subfeature fan1_input: Can't read"

  $sensors_ref = decode_json $sensors_json;

  # my $ambient_temp = ambient_temp();
  # if ($ambient_temp > $default_threshold) {
  my $exhaust_temp = exhaust_temp();
  if ($exhaust_temp > $default_exhaust_threshold) {
    #print "fallback because of high ambient temperature $ambient_temp > $default_threshold\n";
    print "fallback because of high exhaust temperature $exhaust_temp > $default_exhaust_threshold\n";
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
  if (time - $last_print_stats > 60) {
    $current_mode="reset"; # just in case the RAC has rebooted, it
                           # will go back into default control, so
                           # make sure we set it appropriately once
                           # per minute
    $last_print_stats=time;
    $print_stats = 1 if !$quiet;
  }
 nextpoll:
  sleep_and_check_for_exit $cpu_poll_interval;
}
