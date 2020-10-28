#!/usr/bin/env python3
import argparse
import sys, os, os.path
import csv
import re
import math

parser = argparse.ArgumentParser()
parser.add_argument('infile', metavar='INFILE.csv', type=argparse.FileType('r'),
                    help='input log files')

def readfile(f):
    freader = csv.DictReader(f)
    fields = freader.fieldnames
    rows = list(freader)
    f.close()
    return fields, rows

def split_to_kinds(data):
    rows_by_kind = {}
    for row in data:
        if row['param kind'] not in rows_by_kind.keys(): rows_by_kind[row['param kind']] = []
        rows_by_kind[row['param kind']].append(row)
    ret = {}
    for kind, rows in rows_by_kind.items():
        headings = sorted(set(k for row in rows for k, v in row.items() if k != 'param kind' and v is not None and v != ''))
        headings = [k for k in headings if k.startswith('param ')] + [k for k in headings if not k.startswith('param ')]
        for k in headings:
            if any(row[k] is None or row[k] == '' for row in rows):
                # print('Warning: Mix of empty and non-empty entries for key %s in kind %s:\n%s' % (k, kind, repr([row[k] for row in rows])), file=sys.stderr)
                pass
        ret[kind] = ([tuple(k.replace(' ', '-').replace('_', '-') for k in headings)] +
                     [tuple(row[k] for k in headings) for row in rows])
    return ret

def emit_output(kind, rows):
    with open('%s.txt' % kind.replace('_', '-').replace(' ', '-'), 'w') as f:
        f.write('\n'.join(','.join(v.replace(',', '-') for v in row) for row in rows))

if __name__ == '__main__':
    args = parser.parse_args()
    fields, data = readfile(args.infile)
    for kind, rows in split_to_kinds(data).items():
        emit_output(kind, rows)
