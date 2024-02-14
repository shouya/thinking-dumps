use std::time::Instant;

use nix::{
  sched::{self, CpuSet},
  unistd::Pid,
};

// the buffer will take 8M * 8B = 64MB memory
const BUFFER_SIZE: usize = 8 * 1024 * 1024;
const BUCKET_COUNT: usize = 100;

pub fn probe() {
  let mut cpu_set = CpuSet::new();
  cpu_set.set(0).unwrap();
  sched::sched_setaffinity(Pid::from_raw(0), &cpu_set).unwrap();

  let mut durations = vec![0u64; BUFFER_SIZE];
  let mut last = Instant::now();

  // collecting buffer
  for elapsed in &mut durations {
    *elapsed = last.elapsed().as_nanos() as u64;
    last = Instant::now();
  }

  // statistics analysis: draw a histogram of the time intervals
  // discard the largest 0.001% and the smallest 0.001% of the time intervals
  durations.sort_unstable();
  let min = durations[BUFFER_SIZE / 100000];
  let max = durations[BUFFER_SIZE - BUFFER_SIZE / 100000];

  let bucket_size = (max - min).checked_div(BUCKET_COUNT as u64).unwrap_or(1);

  let mut buckets = [0usize; BUCKET_COUNT];
  for duration in durations {
    let bucket =
      (duration - min).checked_div(bucket_size).unwrap_or(0) as usize;
    if bucket < BUCKET_COUNT {
      buckets[bucket] += 1;
    }
  }

  // print the histogram
  for (i, &count) in buckets.iter().enumerate() {
    if count == 0 {
      continue;
    }
    let lower_bound = min + i as u64 * bucket_size;
    let upper_bound = min + (i + 1) as u64 * bucket_size;
    println!(
      "{:6}ns - {:6}ns ({:8}) | {}",
      lower_bound,
      upper_bound - 1,
      count,
      "*".repeat(count.ilog2() as usize + 1)
    );
  }
}

/*
Here's a sample result:

    11ns -     13ns ( 6725996) | ***********************
    14ns -     16ns ( 1659127) | *********************
    17ns -     19ns (    2042) | ***********
    20ns -     22ns (     200) | ********
    23ns -     25ns (     107) | *******
    26ns -     28ns (     227) | ********
    29ns -     31ns (     195) | ********
    32ns -     34ns (      86) | *******
    35ns -     37ns (      62) | ******
    38ns -     40ns (      28) | *****
    41ns -     43ns (      18) | *****
    44ns -     46ns (      20) | *****
    47ns -     49ns (      11) | ****
    50ns -     52ns (      33) | ******
    53ns -     55ns (      12) | ****
    56ns -     58ns (       7) | ***
    59ns -     61ns (       2) | **
    62ns -     64ns (       3) | **
    65ns -     67ns (       7) | ***
    68ns -     70ns (       5) | ***
    71ns -     73ns (       4) | ***
    74ns -     76ns (       5) | ***
    77ns -     79ns (       3) | **
    83ns -     85ns (       1) | *
    86ns -     88ns (       1) | *
    89ns -     91ns (       2) | **
    92ns -     94ns (       2) | **
    95ns -     97ns (       3) | **
    98ns -    100ns (       1) | *
   101ns -    103ns (       2) | **
   104ns -    106ns (       4) | ***
   107ns -    109ns (       3) | **
   110ns -    112ns (       1) | *
   113ns -    115ns (       5) | ***
   116ns -    118ns (       3) | **
   119ns -    121ns (       2) | **
   122ns -    124ns (       1) | *
   125ns -    127ns (       1) | *
   128ns -    130ns (       3) | **
   131ns -    133ns (       3) | **
   134ns -    136ns (       3) | **
   140ns -    142ns (       2) | **
   143ns -    145ns (       2) | **
   146ns -    148ns (       1) | *
   149ns -    151ns (       2) | **
   155ns -    157ns (       4) | ***
   161ns -    163ns (       1) | *
   164ns -    166ns (       1) | *
   167ns -    169ns (       2) | **
   170ns -    172ns (       2) | **
   173ns -    175ns (       1) | *
   176ns -    178ns (       3) | **
   182ns -    184ns (       3) | **
   188ns -    190ns (       3) | **
   191ns -    193ns (       1) | *
   197ns -    199ns (       1) | *
   200ns -    202ns (      17) | *****
   203ns -    205ns (      35) | ******
   206ns -    208ns (      20) | *****
   209ns -    211ns (      52) | ******
   212ns -    214ns (      43) | ******
   215ns -    217ns (       8) | ****
   218ns -    220ns (       8) | ****
   221ns -    223ns (       7) | ***
   224ns -    226ns (       9) | ****
   227ns -    229ns (       6) | ***
   230ns -    232ns (       1) | *
   233ns -    235ns (       1) | *
   245ns -    247ns (       1) | *
   248ns -    250ns (       1) | *
   254ns -    256ns (       1) | *
   257ns -    259ns (       1) | *
   260ns -    262ns (       1) | *
   275ns -    277ns (       1) | *
   284ns -    286ns (       1) | *
   290ns -    292ns (       1) | *
   293ns -    295ns (       1) | *
   302ns -    304ns (       1) | *
   305ns -    307ns (       1) | *
   308ns -    310ns (       1) | *

From which I estimate the context switch time to be around 200-220ns. (or 50-55ns?)
*/
