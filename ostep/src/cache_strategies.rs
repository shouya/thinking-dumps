//! ## Cache strategy playground

//! This module contains a simple cache simulator and a few
//! replacement strategies.
//

#![allow(clippy::upper_case_acronyms)]
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone)]
struct Cache<T> {
  // A cache is a set of values of a given max size N.
  values: Box<[Option<T>]>,
}

impl<T: PartialEq> Cache<T> {
  fn new(size: usize) -> Self {
    let mut values = vec![];
    for _ in 0..size {
      values.push(None);
    }

    // can't use vec![None; size] because it would require T to
    // implement Clone which is actually not necessary
    Cache {
      values: values.into_boxed_slice(),
    }
  }

  fn size(&self) -> usize {
    self.values.len()
  }

  fn iter(&self) -> impl Iterator<Item = &T> {
    self.values.iter().filter_map(|x| x.as_ref())
  }

  fn contains(&self, v: &T) -> bool
  where
    T: PartialEq,
  {
    self.find(v).is_some()
  }

  fn find(&self, v: &T) -> Option<usize>
  where
    T: PartialEq,
  {
    self.iter().position(|x| x == v)
  }

  fn find_empty_slot(&self) -> Option<usize> {
    self.values.iter().position(|x| x.is_none())
  }

  fn insert(&mut self, v: T, i: usize) -> bool {
    if self.values[i].is_none() {
      self.values[i] = Some(v);
      return true;
    }

    false
  }

  // returns whether the action is valid.
  fn take_action(&mut self, action: &Action, new: T) -> bool {
    match *action {
      Action::Insert => self
        .find_empty_slot()
        .is_some_and(|loc| self.insert(new, loc)),
      Action::InsertAt(loc) => self.insert(new, loc),
      Action::ReplaceAt(loc) => {
        self.values[loc] = Some(new);
        true
      }
      Action::ReplaceBecauseFull(loc) => {
        self.values[loc] = Some(new);
        true
      }
    }
  }

  fn is_full(&self) -> bool {
    self.values.iter().all(|x| x.is_some())
  }
}

#[derive(Clone, Copy, Debug)]
// the difference between ReplaceAt and ReplaceBecauseFull is that the
// first may count as conflict miss or cold miss, and the second
// always as capacity miss.
enum Action {
  Insert,
  InsertAt(usize),
  ReplaceAt(usize),
  ReplaceBecauseFull(usize),
}

trait ReplacementStrategy<T> {
  fn init(&mut self, _cache: &Cache<T>) {}
  fn on_hit(&mut self, _key: &T, _cache: &Cache<T>) {}
  fn on_miss(&mut self, key: &T, cache: &Cache<T>) -> Action;

  fn visit(&mut self, key: &T, cache: &Cache<T>) -> Option<Action>
  where
    T: PartialEq,
  {
    if cache.contains(key) {
      self.on_hit(key, cache);
      return None;
    }

    Some(self.on_miss(key, cache))
  }
}

#[derive(Clone)]
struct Evaluator<T> {
  input: Vec<T>,
}

#[derive(Default, Debug)]
struct MissReport {
  cold: usize,
  conflict: usize,
  capacity: usize,
}

struct EvaluationReport {
  hits: usize,
  misses: MissReport,
}

impl EvaluationReport {
  fn new() -> Self {
    EvaluationReport {
      hits: 0,
      misses: Default::default(),
    }
  }

  fn hit_rate(&self) -> f64 {
    self.hits as f64 / (self.hits + self.total_misses()) as f64
  }

  fn total_misses(&self) -> usize {
    self.misses.cold + self.misses.conflict + self.misses.capacity
  }
}

impl<T: Debug> Evaluator<T> {
  fn update_report(&self, report: &mut EvaluationReport, action: &Action) {
    match action {
      Action::Insert | Action::InsertAt(_) => {
        report.misses.cold += 1;
      }
      Action::ReplaceBecauseFull(_) => {
        report.misses.capacity += 1;
      }
      Action::ReplaceAt(_) => {
        // I'm not sure whether we can count it as a cold miss if the
        // slot is empty currently.
        // report.misses.cold += 1;
        report.misses.conflict += 1;
      }
    }
  }

  fn evaluate(
    &mut self,
    mut strategy: impl ReplacementStrategy<T>,
    cache_size: usize,
  ) -> EvaluationReport
  where
    T: Clone + PartialEq,
  {
    let mut report = EvaluationReport::new();
    let mut cache = Cache::new(cache_size);

    strategy.init(&cache);

    for input in self.input.iter() {
      let Some(action) = strategy.visit(input, &cache) else {
        report.hits += 1;
        continue;
      };

      self.update_report(&mut report, &action);

      if !cache.take_action(&action, input.clone()) {
        eprintln!("Invalid action {:?}", action);
      }
    }

    report
  }
}

mod strategies {
  use std::hash::{DefaultHasher, Hasher};

  use super::*;
  // All data structures implemented here just for simplicity and
  // educational purpose. They are not optimized for performance
  // whatosever.

  #[derive(Default)]
  pub struct FIFO {
    i: usize,
  }

  impl<T: PartialEq + Clone + Debug> ReplacementStrategy<T> for FIFO {
    fn on_miss(&mut self, _key: &T, cache: &Cache<T>) -> Action {
      if !cache.is_full() {
        return Action::Insert;
      }

      let to_remove = self.i;
      self.i += 1;
      self.i %= cache.size();
      Action::ReplaceBecauseFull(to_remove)
    }
  }

  #[derive(Default)]
  pub struct LRU {
    last_visit: Vec<usize>,
    tick: usize,
  }

  impl<T: PartialEq + Clone + Debug> ReplacementStrategy<T> for LRU {
    fn init(&mut self, cache: &Cache<T>) {
      self.last_visit = vec![0; cache.size()];
    }

    fn on_hit(&mut self, key: &T, cache: &Cache<T>) {
      self.tick += 1;
      let i = cache.find(key).unwrap();
      self.last_visit[i] = self.tick;
    }

    fn on_miss(&mut self, _key: &T, cache: &Cache<T>) -> Action {
      self.tick += 1;

      if !cache.is_full() {
        let slot = cache.find_empty_slot().unwrap();
        self.last_visit[slot] = self.tick;
        return Action::InsertAt(slot);
      }

      let oldest_entry = self
        .last_visit
        .iter()
        .enumerate()
        .min_by_key(|x| x.1)
        .unwrap()
        .0;
      self.last_visit[oldest_entry] = self.tick;
      Action::ReplaceBecauseFull(oldest_entry)
    }
  }

  /// Belady's optimal policy: replace the value in cache that will be
  /// accessest furthest in the future.
  pub struct BeladyOptimal<T> {
    future_values: Vec<T>,
  }

  impl<T> BeladyOptimal<T> {
    pub fn new(input: Vec<T>) -> Self {
      BeladyOptimal {
        future_values: input,
      }
    }

    fn future_distance(&self, v: &T) -> Option<usize>
    where
      T: PartialEq,
    {
      self.future_values.iter().position(|x| x == v)
    }
  }

  impl<T: PartialEq + Clone + Debug> ReplacementStrategy<T> for BeladyOptimal<T> {
    fn on_hit(&mut self, key: &T, _cache: &Cache<T>) {
      assert!(self.future_values.remove(0) == *key);
    }

    fn on_miss(&mut self, key: &T, cache: &Cache<T>) -> Action {
      assert!(self.future_values.remove(0) == *key);

      if !cache.is_full() {
        return Action::Insert;
      }

      let max = cache
        .iter()
        .max_by_key(|x| self.future_distance(x).unwrap_or(usize::MAX))
        .unwrap();
      let loc = cache.find(max).unwrap();
      Action::ReplaceBecauseFull(loc)
    }
  }

  #[derive(Default)]
  pub struct HashSlot {}

  impl<T: Hash + PartialEq> ReplacementStrategy<T> for HashSlot {
    fn on_miss(&mut self, key: &T, cache: &Cache<T>) -> Action {
      let mut hasher = DefaultHasher::new();
      key.hash(&mut hasher);
      let index = hasher.finish() % cache.size() as u64;

      if !cache.is_full() {
        return Action::InsertAt(index as usize);
      }

      Action::ReplaceAt(index as usize)
    }

    fn visit(&mut self, input: &T, cache: &Cache<T>) -> Option<Action> {
      if cache.contains(input) {
        return None;
      }

      let mut hasher = DefaultHasher::new();
      input.hash(&mut hasher);
      let index = hasher.finish() % cache.size() as u64;
      Some(Action::ReplaceAt(index as usize))
    }
  }

  // The clock algorithm is a replacement strategy approximating LRU
  // with a lower (amortized) time and space complexity.
  #[derive(Default)]
  pub struct Clock {
    used: Vec<bool>,
    hand: usize,
  }

  impl Clock {
    fn next(&mut self) -> usize {
      loop {
        if self.used[self.hand] {
          self.used[self.hand] = false;
          self.hand += 1;
          self.hand %= self.used.len();
        } else {
          return self.hand;
        }
      }
    }
  }

  impl ReplacementStrategy<usize> for Clock {
    fn init(&mut self, cache: &Cache<usize>) {
      self.used = vec![false; cache.size()];
    }

    fn on_hit(&mut self, key: &usize, cache: &Cache<usize>) {
      self.used[cache.find(key).unwrap()] = true;
    }

    fn on_miss(&mut self, _key: &usize, cache: &Cache<usize>) -> Action {
      if !cache.is_full() {
        let slot = cache.find_empty_slot().unwrap();
        self.used[slot] = true;
        return Action::InsertAt(slot);
      }

      let slot = self.next();
      self.used[slot] = true;
      Action::ReplaceAt(slot)
    }
  }
}

pub mod demo {
  #![allow(unused)]
  use super::*;
  use strategies::*;

  pub fn belady_optimal_demo() {
    let mut evaluator = Evaluator {
      input: vec![1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5],
    };

    for cache_size in 1..5 {
      print!("size {}: ", cache_size);

      let report = evaluator
        .evaluate(BeladyOptimal::new(evaluator.input.clone()), cache_size);
      print!("Belady({:.2}) ", report.hit_rate());

      let report = evaluator.evaluate(FIFO::default(), cache_size);
      print!("FIFO({:.2}) ", report.hit_rate());

      let report = evaluator.evaluate(LRU::default(), cache_size);
      print!("LRU({:.2}) ", report.hit_rate());

      let report = evaluator.evaluate(Clock::default(), cache_size);
      print!("Clock({:.2}) ", report.hit_rate());

      println!();
    }
  }

  pub fn belady_anomaly_demo() {
    let mut evaluator = Evaluator {
      input: vec![1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5],
    };

    let report_fifo_3 = evaluator.evaluate(FIFO::default(), 3);
    let report_fifo_4 = evaluator.evaluate(FIFO::default(), 4);
    println!(
      "FIFO: {:.2} (3) -> {:.2} (4)",
      report_fifo_3.hit_rate(),
      report_fifo_4.hit_rate()
    );

    let report_lru_3 = evaluator.evaluate(LRU::default(), 3);
    let report_lru_4 = evaluator.evaluate(LRU::default(), 4);
    println!(
      "LRU : {:.2} (3) -> {:.2} (4)",
      report_lru_3.hit_rate(),
      report_lru_4.hit_rate()
    );
  }

  // The three C's of cache misses: cold, conflict, capacity
  pub fn three_c() {
    let mut evaluator = Evaluator {
      input: vec![1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5],
    };

    fn show_report(name: &str, report: &EvaluationReport) {
      println!(
        "{:7}: {:3}v{:<3} (cold: {:2}; cflt: {:2}; cpcy: {:2}), hit rate: {:.2}",
        name,
        report.hits,
        report.total_misses(),
        report.misses.cold,
        report.misses.conflict,
        report.misses.capacity,
        report.hit_rate()
      );
    }

    let report_fifo = evaluator.evaluate(FIFO::default(), 3);
    show_report("FIFO", &report_fifo);

    let report_hash = evaluator.evaluate(HashSlot::default(), 3);
    show_report("Hash", &report_hash);

    let report_lru = evaluator.evaluate(LRU::default(), 3);
    show_report("LRU", &report_lru);

    let report_belady =
      evaluator.evaluate(BeladyOptimal::new(evaluator.input.clone()), 3);
    show_report("Belady", &report_belady);
  }

  pub fn demo() {
    println!("Belady's optimal policy demo:");
    belady_optimal_demo();
    println!("\nBelady's anomaly demo:");
    belady_anomaly_demo();
    println!("\nThree C's of cache misses:");
    three_c();
  }
}
