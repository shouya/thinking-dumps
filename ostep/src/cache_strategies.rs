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
    self.iter().any(|x| x == v)
  }

  fn replace(&mut self, old: T, new: T) -> bool {
    for val in self.values.iter_mut().filter_map(|x| x.as_mut()) {
      if val == &old {
        *val = new;
        return true;
      }
    }
    false
  }

  fn insert(&mut self, v: T) -> bool {
    let slot = self.values.iter_mut().find(|x| x.is_none());
    if let Some(slot) = slot {
      let _ = slot.insert(v);
      return true;
    }
    false
  }

  // returns whether the action is valid.
  fn take_action(&mut self, action: Action<T>, new: T) -> bool {
    match action {
      Action::Insert => self.insert(new),
      Action::ReplaceAt(loc) => {
        self.values[loc] = Some(new);
        true
      }
      Action::ReplaceBecauseFull(old) => self.replace(old, new),
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
enum Action<T> {
  ReplaceAt(usize),
  ReplaceBecauseFull(T),
  Insert,
}

trait ReplacementStrategy<T> {
  fn visit(&mut self, input: &T, cache: &Cache<T>) -> Option<Action<T>>;
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
  fn update_report(&self, report: &mut EvaluationReport, action: &Action<T>) {
    match action {
      Action::Insert => {
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

    for input in self.input.iter() {
      let Some(action) = strategy.visit(input, &cache) else {
        report.hits += 1;
        continue;
      };

      self.update_report(&mut report, &action);

      if !cache.take_action(action.clone(), input.clone()) {
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
  pub struct FIFO<T> {
    queue: Vec<T>,
  }

  impl<T: PartialEq + Clone + Debug> ReplacementStrategy<T> for FIFO<T> {
    fn visit(&mut self, input: &T, cache: &Cache<T>) -> Option<Action<T>> {
      if cache.contains(input) {
        return None;
      }

      if !cache.is_full() {
        self.queue.push(input.clone());
        return Some(Action::Insert);
      }

      let to_remove = self.queue.remove(0);
      self.queue.push(input.clone());
      Some(Action::ReplaceBecauseFull(to_remove))
    }
  }

  #[derive(Default)]
  pub struct LRU<T> {
    queue: Vec<T>,
  }

  impl<T: PartialEq + Clone + Debug> ReplacementStrategy<T> for LRU<T> {
    fn visit(&mut self, input: &T, cache: &Cache<T>) -> Option<Action<T>> {
      if cache.contains(input) {
        self.queue.retain(|x| x != input);
        self.queue.push(input.clone());
        return None;
      }

      if !cache.is_full() {
        self.queue.push(input.clone());
        return Some(Action::Insert);
      }

      let to_remove = self.queue.remove(0);
      self.queue.push(input.clone());
      Some(Action::ReplaceBecauseFull(to_remove))
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
    fn visit(&mut self, input: &T, cache: &Cache<T>) -> Option<Action<T>> {
      assert!(self.future_values.remove(0) == *input);

      if cache.contains(input) {
        return None;
      }

      if !cache.is_full() {
        return Some(Action::Insert);
      }

      let max = cache
        .iter()
        .max_by_key(|x| self.future_distance(x).unwrap_or(usize::MAX))
        .unwrap();
      Some(Action::ReplaceBecauseFull(max.clone()))
    }
  }

  #[derive(Default)]
  pub struct HashSlot<T> {
    marker: std::marker::PhantomData<T>,
  }

  impl<T: Hash + PartialEq> ReplacementStrategy<T> for HashSlot<T> {
    fn visit(&mut self, input: &T, cache: &Cache<T>) -> Option<Action<T>> {
      if cache.contains(input) {
        return None;
      }

      let mut hasher = DefaultHasher::new();
      input.hash(&mut hasher);
      let index = hasher.finish() % cache.size() as u64;
      Some(Action::ReplaceAt(index as usize))
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
      println!("LRU({:.2}) ", report.hit_rate());
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
