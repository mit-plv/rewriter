#!/usr/bin/env python3
import argparse
import sys, os, os.path
import csv
import re
import math
import string

parser = argparse.ArgumentParser()
parser.add_argument('infile', metavar='INFILE.txt', type=argparse.FileType('r'),
                    help='input txt file')
parser.add_argument('-o', '--output-file', dest='outfile', type=argparse.FileType('w'),
                    default=sys.stdout,
                    help="output file name")

def readfile(f):
    freader = csv.DictReader(f)
    fields = freader.fieldnames
    rows = list(freader)
    f.close()
    return fields, rows

XVAR = 'x'
VARS = ''.join(ch for ch in (string.ascii_lowercase + string.ascii_uppercase) if ch not in XVAR)
def regression_to_formula_vars_inits_printer(formula_kind, extra=''):
    poly_kinds = dict((k, n) for n, k in enumerate(('constant', 'linear', 'quadratic', 'cubic', 'quartic', 'quintic')))
    if formula_kind in poly_kinds.keys():
        deg = poly_kinds[formula_kind]
        var_list = list(VARS[:deg+1])
        inits = [1] * len(var_list)
        formula = ''
        printer = ''
        for e, k in reversed(list(enumerate(reversed(var_list)))):
            if formula != '': formula += '+'
            if printer != '': printer += ', "+", '
            formula += k
            printer += k
            if e != 0:
                formula += f'*{XVAR}'
                printer += f', "*{XVAR}'
                if e != 1:
                    formula += f'**{e}'
                    printer += f'^{e}'
                printer += '"'
        return (formula, var_list, inits, printer)
    elif formula_kind == 'exponential':
        (a, b), x = VARS[:2], XVAR
        return (f'{a}*exp({b}*{x})', [a, b], [1, 1], f'{a}, "*Qexp(", {b}, "*{x})"')
    elif formula_kind == 'factorial':
        (a, ), x = VARS[:1], XVAR
        return (f'{a}*gamma({x}+1)', [a], [1], f'{a}, "*fact({x})"')
    else:
        raise Exception(f'Unknown formula kind: {formula_kind} (extra={extra})')

def make_gnuplot(inname, outname, cols):
    ret = ['set datafile separator ",";',
           f'set print "{outname}";',
           '',
           '']
    xcol = 1
    ENDING = '-real'
    for ncol, col in enumerate(cols):
        if col.startswith('param-') or not col.endswith(ENDING): continue
        ycol = ncol + 1 # gnuplot 1-indexes
        orig_col = col
        col = col[:-len(ENDING)]
        col_kinds = col.split('-regression-')
        col, regression_kinds = col_kinds[0], col_kinds[1:]
        for regression_kind in regression_kinds:
            formula, var_list, inits, printer = regression_to_formula_vars_inits_printer(regression_kind, extra=orig_col)
            ret.append(f'f({XVAR}) = {formula};')
            for var, val in zip(var_list, inits):
                ret.append(f'{var}={val};')
            ret.append(f"fit f({XVAR}) '{inname}' u {xcol}:{ycol} via {','.join(var_list)};")
            ret.append(f'print "{col}-regression-{regression_kind}: ", {printer};')
            ret.append('')
        ret.append('')
    return '\n'.join(ret)

if __name__ == '__main__':
    args = parser.parse_args()
    fields, data = readfile(args.infile)
    ret = make_gnuplot(args.infile.name, args.infile.name + '-fits.dat', fields)
    args.outfile.write(ret)
    args.outfile.close()
