"""Print the import graph of the Lean libraries declared in lakefile.toml as an indented list.

Usage: python tools/depgraph.py

Each Lean file's line lists the files of these libraries that it imports directly (Mathlib imports
are not listed). The BosonicLean folders come in the order of the library's construction: phase
space and covariance matrices first, then the one-mode quantum states, analysis, C*-algebra
facts, the CCR algebra, Gaussian tensor networks and the formal Fock space; any further library
of the lakefile follows, with its files under their library name. Adapted from
LocalAlgebrasLean's tool of the same name.
"""
import os
import re
import tomllib

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')


def libraries():
    """The `[[lean_lib]]` names of lakefile.toml, BosonicLean first."""
    with open(os.path.join(ROOT, 'lakefile.toml'), 'rb') as fh:
        names = [lib['name'] for lib in tomllib.load(fh).get('lean_lib', [])]
    return ['BosonicLean'] + [n for n in names if n != 'BosonicLean']


LIBRARIES = libraries()
FOLDERS = ['PhaseSpace', 'Quantum', 'Analysis', 'CStar', 'Weyl', 'GaussianTNLean', 'Fock',
           'Examples']
IMPORT = re.compile(r'(?m)^import ((?:' + '|'.join(map(re.escape, LIBRARIES))
                    + r')(?:\.\S+)?)\s*$')


def modules():
    out = {}
    for lib in LIBRARIES:
        for dirpath, _, files in os.walk(os.path.join(ROOT, lib)):
            for f in sorted(files):
                if not f.endswith('.lean'):
                    continue
                path = os.path.join(dirpath, f)
                name = os.path.relpath(path, ROOT)[:-5].replace(os.sep, '.')
                with open(path, encoding='utf-8') as fh:
                    out[name] = IMPORT.findall(fh.read())
    return out


def short(name):
    """`BosonicLean.Weyl.Basic` -> `Weyl/Basic`; files of a further library keep their library
    name; a root file keeps its file name."""
    if '.' not in name:
        return name + '.lean'
    lib, rest = name.split('.', 1)
    return rest.replace('.', '/') if lib == 'BosonicLean' else name.replace('.', '/')


def line(n, mods):
    deps = ', '.join('`' + short(d) + '`' for d in mods[n]) or 'Mathlib only'
    return f"`{short(n)}` imports {deps}"


def main():
    mods = modules()
    print('- `BosonicLean/`')
    folders = FOLDERS + sorted({n.split('.')[1] for n in mods
                                if n.startswith('BosonicLean.') and n.count('.') >= 2}
                               - set(FOLDERS))
    for folder in folders:
        names = sorted(n for n in mods
                       if n.startswith('BosonicLean.') and n.count('.') >= 2
                       and n.split('.')[1] == folder)
        if not names:
            continue
        print(f'  - `{folder}/`')
        for n in names:
            print('    - ' + line(n, mods))
    for lib in LIBRARIES[1:]:
        names = sorted(n for n in mods if n.startswith(lib + '.'))
        if names:
            print(f'- `{lib}/`')
            for n in names:
                print('  - ' + line(n, mods))


if __name__ == '__main__':
    main()
