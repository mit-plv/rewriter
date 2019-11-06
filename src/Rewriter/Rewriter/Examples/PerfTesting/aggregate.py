#!/usr/bin/env python3
import argparse
import sys, os, os.path
import csv
import re

parser = argparse.ArgumentParser()
parser.add_argument('-o', '--output-file', dest='outfile', type=argparse.FileType('w'),
                    default=sys.stdout,
                    help="output file name")
parser.add_argument('--mathematica', action='store_true',
                    help="emit a .m Mathematica file rather than a .txt file")
parser.add_argument('infile', metavar='INFILE', nargs='*', type=argparse.FileType('r'),
                    help='input log files')


def process_file(f, data):
    def param_to_tuple(p):
        k, v = p.split('=')
        return (k, int(v))
    reg = re.compile(r'Tactic call (.*?) ran for ([0-9\.]+) secs \(([0-9\.]+)u,([0-9\.]+)s\) \(success\)')
    fdir, fname = os.path.split(f.name)
    fbase, kind = os.path.split(fdir)
    curparams = None
    for line in f.readlines():
        r = reg.match(line.strip())
        if line.startswith('Params: '):
            curparams = tuple([('kind', kind)] + [param_to_tuple(p) for p in line[len('Params: '):].strip().replace(' ', '').split(',')])
            if curparams not in data.keys():
                data[curparams] = {}
        elif line.strip() == '':
            continue
        elif r:
            assert(curparams is not None)
            descr, realt, usert, syst = r.groups()
            data[curparams].update(dict([
                ('%s real' % descr, realt),
                ('%s user' % descr, usert),
                ('%s sys' % descr, syst)
            ]))
        else:
            print('WARNING: unrecognized line:\n' + line, file=sys.stderr)

def data_to_mathematica(data):
    ret = {}
    for params, values in sorted(data.items()):
        assert(params[0][0] == 'kind')
        kind = params[0][1]
        rest_params = params[1:]
        if kind not in ret.keys(): ret[kind] = {'keys':list(k for k, v in rest_params)}
        for k, v in values.items():
            if k not in ret[kind].keys(): ret[kind][k] = []
            ret[kind][k].append([v2 for k2, v2 in rest_params] + [v])
    return ret

def data_to_rows(data):
    for params, values in sorted(data.items()):
        yield dict([('param ' + k, v) for k, v in params] + list(values.items()))

def mathematicaify(v):
    if isinstance(v, list):
        return '{%s}' % ', '.join(map(mathematicaify, v))
    elif isinstance(v, int):
        return str(v)
    else:
        return str(v)

def emit_output(f, data, mathematica=False):
    if mathematica:
        f.write('ClearAll[data];\n')
        data = data_to_mathematica(data)
        for kind, kval in sorted(data.items()):
            f.write('data["%s"]["keys"] := {%s};\n' % (kind, ', '.join('"%s"' % k for k in kval['keys'])))
            f.write('data["%s"]["kinds"] := {%s};\n' % (kind, ', '.join('"%s"' % k for k in sorted(kval.keys()) if k != 'keys')))
            for subkind, skval in sorted(kval.items()):
                if subkind != 'keys':
                    f.write('data["%s"]["%s"] := %s;\n' % (kind, subkind, mathematicaify(skval)))
    else:
        data = list(data_to_rows(data))
        keys = list(sorted(set(k for row in data for k in row.keys())))
        param_keys = [k for k in keys if k.startswith('param ')]
        other_keys = [k for k in keys if not k.startswith('param ')]
        keys = param_keys + other_keys
        fwriter = csv.writer(f, lineterminator="\n")
        fwriter.writerow(keys)
        fwriter.writerows([[row.get(k, '') for k in keys] for row in data])
    f.close()

if __name__ == '__main__':
    args = parser.parse_args()
    data = {}
    for f in args.infile:
        process_file(f, data)
    emit_output(args.outfile, data, mathematica=args.mathematica)
