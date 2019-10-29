#!/usr/bin/env python3
import argparse
import sys, os, os.path
import csv
import re

parser = argparse.ArgumentParser()
parser.add_argument('-o', '--output-file', dest='outfile', type=argparse.FileType('w'),
                    default=sys.stdout,
                    help="output file name")
parser.add_argument('kind', metavar='KIND', type=str,
                    help="the kind of output")
parser.add_argument('infile', metavar='INFILE.csv', type=argparse.FileType('r'),
                    help='input log files')

def readfile(f):
    freader = csv.DictReader(f)
    fields = freader.fieldnames
    rows = list(freader)
    f.close()
    return fields, rows

def process_rows(data, kind):
    def remap(new, old, row):
        if isinstance(old, str):
            return (new, row[old])
        elif callable(old):
            return (new, old(row))
        else:
            raise Exception('Invalid non-str-non-callable: %s (for %s)' % (repr(old), new))
    rows = [row for row in data if row['param kind'] == kind]
    known_kinds = ['LiftLetsMap', 'Plus0Tree', 'SieveOfEratosthenes', 'UnderLetsPlus0']
    if kind not in known_kinds:
        raise Exception('Invalid kind: %s; expected one of %s' % (kind, ', '.join(sorted(known_kinds))))
    elif kind == 'LiftLetsMap':
        keymap = [('list length', 'param n'),
                  ('iteration count', 'param m'),
                  ('term size', (lambda row: row['param n'] * row['param m'])),
                  ('Rewrite_for', 'Rewrite_for_gen user'),
                  ('rewriting', 'rewriting user'),
                  ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                  ('rewrite_strat(topdown,bottomup)', 'rewrite_strat(topdown,bottomup) user'),
                  ('rewrite_strat(bottomup,bottomup)', 'rewrite_strat(bottomup,bottomup) user')]
    elif kind == 'Plus0Tree':
        keymap = [('tree depth', 'param n'),
                  ('extra +0s per node', 'param m'),
                  ('term size', (lambda row: 3 * row['param m'] * (2 ** (row['param n'] - 1)))),
                  ('Rewrite_for', 'Rewrite_for_gen user'),
                  ('rewriting', 'rewriting user'),
                  ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                  ('cbv;rewrite!', 'cbv;rewrite! user'),
                  ('cbv;setoid_rewrite', 'cbv;setoid_rewrite user'),
                  ('cbv;rewrite_strat(topdown)', 'cbv;rewrite_strat(topdown) user'),
                  ('cbv;rewrite_strat(bottomup)', 'cbv;rewrite_strat(bottomup) user')]
    elif kind == 'SieveOfEratosthenes':
        keymap = [('n', 'param n'),
                  ('Rewrite_for', 'Rewrite_for_gen user'),
                  ('rewriting', 'rewriting user'),
                  ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                  ('cbv', 'cbv user'),
                  ('lazy', 'lazy user'),
                  ('vm_compute', 'vm_compute user'),
                  ('native(1)(real)', 'native_compute(1) real'),
                  ('native(2)(real)', 'native_compute(2) real'),
                  ('cbn', 'cbn user'),
                  ('simpl', 'simpl user')]
    elif kind == 'UnderLetsPlus0':
        keymap = [('n', 'param n'),
                  ('Rewrite_for', 'Rewrite_for_gen user'),
                  ('rewriting', 'rewriting user'),
                  ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                  ('cbv;rewrite_strat(bottomup)', 'cbv;rewrite_strat(bottomup) user'),
                  ('cbv;rewrite_strat(topdown)', 'cbv;rewrite_strat(topdown) user'),
                  ('cbv;setoid_rewrite', 'cbv;setoid_rewrite user')]
    else:
        raise Exception('Internal Error: Known but unhandled kind: %s' % kind)
    return tuple(k for k, k_old in keymap), [dict(remap(k, k_old, row) for k, k_old in keymap) for row in rows]

def emit_output(f, fields, rows):
    rows = list(rows)
    fwriter = csv.DictWriter(f, fields)
    fwriter.writeheader()
    fwriter.writerows(rows)
    f.close()

if __name__ == '__main__':
    args = parser.parse_args()
    fields, data = readfile(args.infile)
    fields, rows = process_rows(data, args.kind)
    emit_output(args.outfile, fields, rows)
