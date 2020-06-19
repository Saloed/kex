#!/usr/bin/python

import os
import argparse

parser = argparse.ArgumentParser(description='Collect refinements for given jar')
parser.add_argument('--jar', type=str, required=True, help='jar to analyze')

args = parser.parse_args()

jar_file = os.path.normpath(args.jar)

log_name = '{}.log'.format(os.path.basename(jar_file))
log_path = os.path.join(os.path.dirname(jar_file), 'results')
if not os.path.exists(log_path):
    os.mkdir(log_path)
log_path = os.path.join(log_path, log_name)

kex_args = {
    '--mode': 'refinements',
    '--output': 'hlam/',
    '--jar': jar_file,
    '--log': log_path,
}
print('Running kex with {}'.format(kex_args))

args_str = ' '.join('{} {}'.format(key, val) for key, val in kex_args.items())
os.system('./kex.sh {}'.format(args_str))
