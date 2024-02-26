#!/usr/bin/env python3
import sys
import glob
import csv

def create_cvc4_results(err_file):
    with open(err_file) as f:
        lines = [line.rstrip() for line in f.readlines()]
        prop_name = err_file.removesuffix('.err')
        if 'unsat' in lines[-2]:
            sat_unsat_msg, result = lines[-2].split(', ')
            total_time_msg, time = lines[-1].split(', ')
            assert(sat_unsat_msg == 'driver::sat/unsat')
            assert(total_time_msg == 'driver::totalTime')
            return {
                'name': prop_name,
                'result': result == 'unsat',
                'time': float(time),
            }
        else:
            return {
                'name': prop_name,
                'result': False,
                'time': 0.0,
            }

if __name__ == '__main__':
    cvc4_dir = sys.argv[1]
    results_file = sys.argv[2]
    with open(results_file, 'w') as f:
        writer = csv.DictWriter(f, ['name', 'result', 'time'])
        writer.writeheader()
        for err_file in glob.glob(cvc4_dir + '/*.err'):
            writer.writerow(create_cvc4_results(err_file))
