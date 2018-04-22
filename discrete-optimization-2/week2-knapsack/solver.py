# -*- coding: utf-8 -*-
#!/usr/bin/python

import sys
import subprocess
import time
import os

PROBLEM_SPEC = {
  'timeout': 10, # 10 secs
  'objective': 'maximize',
  'algorithms': {
    'brutal': {
      'scale-max': 35
    },
    'greedy': {},
    'dp': {
      'scale-max': 400
    }
  },
  'parse_scale': lambda inp: int(inp.split('\n')[0].split(' ')[0]),
  'parse_objective': lambda outp: int(outp.split('\n')[0].split(' ')[0]),
  'parse_optimal': lambda outp: bool(int(outp.split('\n')[0].split(' ')[1]))
}

def fit_size(spec, n):
  if spec is None:
    return True

  min_ = spec.get('scale-min', -1)
  max_ = spec.get('scale-max', -1)

  if min_ != -1 and n < min_:
    return False
  if max_ != -1 and n > max_:
    return False

  return True

def run_algorithm(alg, input_data, timeout = None):
  file_name = f"{alg}.hs"
  solution = {}
  solution['name'] = alg

  start_time = time.time()
  try:
    proc = subprocess.run(["stack", "runghc", file_name],
                          input=input_data.encode(),
                          stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE,
                          timeout=timeout)
    proc.check_returncode()
    solution['completed'] = True
  except subprocess.TimeoutExpired:
    solution['completed'] = False
  except CalledProcessError:
    solution['completed'] = False
  finally:
    solution['time'] = time.time() - start_time

  if not solution['completed']:
    return solution

  output = proc.stdout.decode('utf-8')
  solution['output'] = output
  solution['optimal'] = PROBLEM_SPEC['parse_optimal'](output)
  solution['objective'] = PROBLEM_SPEC['parse_objective'](output)

  return solution



def solve_it(input_data):
  scale = PROBLEM_SPEC['parse_scale'](input_data)
  possible_alg = [(alg,spec) for alg, spec in PROBLEM_SPEC['algorithms'].items()
                  if fit_size(spec, scale)]

  global_timeout = PROBLEM_SPEC.get('timeout', 60*1000)

  os.chdir("algorithms/")
  solutions = []
  for (alg,spec) in possible_alg:
    alg_timeout = spec.get('timeout', global_timeout)
    print(f"Running against algorithm {alg}...", file=sys.stderr)
    solution = run_algorithm(alg, input_data, timeout=alg_timeout)
    if solution['completed']:
      print(f"Time: {solution['time']}, " + \
            f"Objective: {solution['objective']}, " + \
            f"Optimal: {solution['optimal']}",
            file=sys.stderr)
    else:
      print(f"Time: {solution['time']}, not complete",
            file=sys.stderr)
    solutions.append(solution)

  os.chdir("../")
  print("All algorithms tested, evaluating performances.", file=sys.stderr)

  feasible_solutions = [sol for sol in solutions if sol['completed']]
  optimal_solutions = [sol for sol in feasible_solutions if sol['optimal']]

  if optimal_solutions:
    best_solution = optimal_solutions[0]
    print(f"Optimal solution is done with {best_solution['name']}, " + \
          f"Achieving objective of {best_solution['objective']}",
          file=sys.stderr)
    return best_solution['output']

  objective = PROBLEM_SPEC.get('objective', 'minimize')

  if objective == 'minimize':
    comparison_key = lambda sol: sol['objective']
  else:
    comparison_key = lambda sol: -sol['objective']

  try:
    best_solution = min(feasible_solutions, key=comparison_key)
  except ValueError:
    best_solution = None

  if best_solution:
    print(f"Best solution is done with {best_solution['name']}, " + \
          f"Achieving objective of {best_solution['objective']}",
          file=sys.stderr)
    return best_solution['output']
  else:
    print(f'No solution found', file=sys.stderr)
    return ''

if __name__ == '__main__':
    import sys
    if len(sys.argv) > 1:
        file_location = sys.argv[1].strip()
        with open(file_location, 'r') as input_data_file:
            input_data = input_data_file.read()
        print(solve_it(input_data))
    else:
        print('This test requires an input file.  Please select one from the data directory. (i.e. python solver.py ./data/ks_4_0)')
