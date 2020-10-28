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
    REPLACE_KEY = '#replace-'
    def param_to_tuple(p):
        k, v = p.split('=')
        if k.startswith(REPLACE_KEY): return (k, v.split('|'))
        try:
            return (k, int(v))
        except ValueError:
            return (k, v)
    reg = re.compile(r'(?:Tactic call|Finished) (.*?) (?:ran for|in) ([0-9\.]+) secs \(([0-9\.]+)u,([0-9\.]+)s\)(?: \(success\)| \(successful\))?')
    native_reg = re.compile(r'native_compute: (.*?) done in ([0-9\.]+)')
    fdir, fname = os.path.split(f.name)
    fbase, kind = os.path.split(fdir)
    curparams = None
    cur_native_data = {}
    cur_replacements = {}
    for line in f.readlines():
        r = reg.match(line.strip())
        nr = native_reg.match(line.strip())
        if line.startswith('Params: '):
            curparams = tuple([('kind', kind)] + [param_to_tuple(p) for p in line[len('Params: '):].strip().replace(' ', '').split(',')])
            cur_replacements = {k[len(REPLACE_KEY):]: v for k, v in curparams if k.startswith(REPLACE_KEY)}
            curparams = tuple((k, v) for k, v in curparams if not k.startswith(REPLACE_KEY))
            if curparams not in data.keys():
                data[curparams] = {}
        elif line.strip() == '':
            continue
        elif r:
            assert(curparams is not None)
            descr, realt, usert, syst = r.groups()
            if len(cur_replacements.get(descr, [])) > 0:
                descr = cur_replacements[descr].pop(0)
            data[curparams].update(dict([
                ('%s real' % descr, realt),
                ('%s user' % descr, usert),
                ('%s sys' % descr, syst)
            ] + [
                ('%s %s real' % (re.sub(r'-regression-.*', '', descr), k), v)
                for k, v in cur_native_data.items()
            ]))
            cur_native_data = {}
        elif nr:
            native_descr, realt = nr.groups()
            native_descr = 'native_compute ' + native_descr.lower()
            if len(cur_replacements.get(native_descr, [])) > 0:
                native_descr = cur_replacements[native_descr].pop(0)
            if native_descr in cur_native_data.keys():
                print('WARNING: overwriting key %s (value %s) with %s' % (native_descr, cur_native_data[native_descr], realt), file=sys.stderr)
            cur_native_data[native_descr] = realt
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
