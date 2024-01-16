import subprocess
import argparse
import pathlib
import csv

# 30s time limit
DEFAULT_TIME_LIMIT_MS = 30000

# Assumed UTF-8
SHELL_ENCODING = 'utf-8'

def make_cvc5_i_args(time_limit):
    # --stats and --tlimit required for timing and file info
    # All other required for running in inductive theorem proving mode
    # (see https://lara.epfl.ch/~reynolds/VMCAI2015-ind/)
    return ['--quant-ind', '--full-saturate-quant', '--stats', '--tlimit', str(time_limit)]

def make_cvc5_ig_args(time_limit):
    # --stats required for timing and file info
    # All other required for running in theory exploration theorem proving mode
    # (see https://lara.epfl.ch/~reynolds/VMCAI2015-ind/)
    return ['--quant-ind',  '--conjecture-gen', '--conjecture-gen-per-round=3', '--full-saturate-quant', '--stats', '--tlimit', str(time_limit)]

def run_file(cvc5_binary, filename, cvc5_args, quiet=False):
    '''
    Runs an SMT2 file containing a theorem and returns whether it was proven
    successfully and the time taken
    '''
    if filename.suffix != '.smt2':
        if not quiet:
            print(f'File not SMT2, skipping: {filename}')
        return None
    res = subprocess.run([cvc5_binary.absolute(), *cvc5_args, filename.absolute()],
                         capture_output=True)
    stdout = res.stdout.decode(SHELL_ENCODING)
    stderr = res.stderr.decode(SHELL_ENCODING)
    stderr_lines = stderr.split('\n')
    # The first line either says unsat or interrupted by timeout
    success = stdout.startswith('unsat')
    time = find_time(stderr_lines)
    return ('success' if success else stderr_lines[0], time)

def find_time(stdout_lines):
    '''
    When --stats is enabled, time is output as

    global::totalTime = TIME_WITH_UNITS

    Extract this line from the output
    '''
    for line in stdout_lines:
        if line.startswith('global::totalTime'):
            [lhs, rhs] = line.split(' = ')
            return rhs

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        prog='CVC5 Inductive Benchmark Runner',
        description='Runs CVC5 inductive benchmarks, collecting the results.',
        )

    parser.add_argument('cvc5_binary', type=pathlib.Path,
                        help='CVC5 binary (v1.5 recommended)',
                        )
    parser.add_argument('target', type=pathlib.Path,
                        help='SMT2 file or directory containing SMT2 files to run CVC5 on.',
                        )
    parser.add_argument('-t', '--timeout', type=int,
                        default=DEFAULT_TIME_LIMIT_MS,
                        help='Time limit for each CVC5 run.',
                        )
    parser.add_argument('-o', '--output', type=pathlib.Path,
                        help='Write the results as a CSV to',
                        )
    parser.add_argument('-q', '--quiet',
                        help='Suppress output.',
                        )
    parser.add_argument('-g', '--theory-exploration', action='store_true',
                        help='Runs CVC5 in theory exploration mode (defaults to inductive mode).',
                        )

    args = parser.parse_args()
    cvc5_binary = args.cvc5_binary
    timeout = args.timeout
    target = args.target
    output = args.output
    quiet = args.quiet

    assert(cvc5_binary.is_file())
    assert(target.is_dir() or target.is_file())

    if not quiet:
        print(f'Running CVC5 in {"theory exploration" if args.theory_exploration else "inductive"} mode')

    cvc5_args = make_cvc5_ig_args(timeout) if args.theory_exploration else make_cvc5_i_args(timeout)

    filenames = []
    if target.is_file():
        filenames = [target]
    if target.is_dir():
        filenames = sorted(target.iterdir())

    results = []
    for filename in filenames:
        run_result = run_file(cvc5_binary, filename, cvc5_args, quiet)
        if run_result:
            result, time = run_result
            if not quiet:
                print(filename)
                print(f'Result: {result}')
                print(f'Time: {time}')
            with open(filename, 'r') as smt_file:
                # Hack: the 3rd line from the last contains the prop
                # Using their formatting the nicer thing to do would
                # be to search for the line with the comment
                #
                #     ; G85
                #
                # where 85 is replaced by whatever number goal the file is.
                prop = smt_file.readlines()[-4].strip()
            results.append({'name': filename.name, 'result': result, 'time': time, 'prop': prop})
    if output:
        with open(output, 'w', newline='') as csvfile:
            fieldnames = ['name', 'result', 'time', 'prop']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for result in results:
                writer.writerow(result)
