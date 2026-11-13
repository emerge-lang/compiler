#!/usr/bin/env python3
"""
Checks the names of the binders in the statements of the lemmas against the naming scheme in the readme
("Names of binders"): a short name (at most three letters, digits and primes aside) always stands for the same
kind of thing, so that `n` is fuel wherever it occurs. Longer, descriptive names are always allowed.

It reads what `Print Module` makes of the theories (verify.sh produces that), as the printed statements carry
the type of every binder, also of those whose type the source leaves to inference.

usage: binder_names.py PRINTED [--report]
Exits 1 if a binder breaks the scheme, listing each.
"""
import collections
import re
import sys

# name -> the kinds of thing it stands for; a kind is the printed type, module qualifiers and spaces removed,
# or fn / fn->bool / fn->Prop for functions
SCHEME = {
    'n': {'nat'}, 'd': {'nat'}, 'k': {'nat'}, 'i': {'nat'}, 'j': {'nat'},
    't': {'EType'}, 'a': {'EType'}, 'x': {'EType'}, 'y': {'EType'}, 'z': {'EType'},
    'C': {'EType'}, 'P': {'EType'}, 'A': {'EType'}, 'B': {'EType'}, 'V': {'EType'},
    'xs': {'listEType'}, 'ys': {'listEType'}, 'zs': {'listEType'}, 'cs': {'listEType'},
    'Ps': {'listEType'}, 'As': {'listEType'},
    'ps': {'listTypeParameterId'}, 'vs': {'listTypeParameterId'},
    'c': {'Class'}, 'sub': {'Class'},
    'm': {'Mutability', 'optionMutability'}, 'gm': {'optionMutability'}, 'ms': {'listMutability'},
    'o': {'Ownership'}, 'v': {'Variance'}, 'g': {'GenericRef'}, 'nn': {'bool'},
    'p': {'TypeParameterId'}, 'q': {'TypeParameterId'},
    'b': {'Bindings', 'list(TypeParameterId*EType)'},
    's': {'VariableStates', 'list(TypeParameterId*VariableState)'}, 'st': {'VariableState'},
    'uf': {'UnifyFn'}, 'u': {'Unification', 'optionUnification'},
    'f': {'fn', 'fn->bool', 'fn->Prop'},
    'Q': {'fn->bool', 'fn->Prop'}, 'R': {'fn->bool', 'fn->Prop'}, 'W': {'fn->bool', 'fn->Prop'},
    'T': {'Type', 'Set'}, 'l': {'list*'},
    'r': {'Alias'}, 'rs': {'Aliasing', 'listAlias'},
    # TokenGuarantee.v has an environment of its own, over the classes of a program
    'env': {'Environment', 'EnvironmentBase'},
}
# <concept><role>: the concept of the target, the assignee, the receiver, the bound, the object at run time, the
# parameter type, or of x, y, z; Qa, Qb are predicates on assignees and on bounds
CONCEPTS = {'m', 'c', 'v', 'o', 'g', 'Q'}
ROLES = {'t', 'a', 'r', 'b', 'o', 'p', 'x', 'y', 'z'}
# the things of the model; a short binder of one of these takes its name from the scheme. Binders of other types
# (bool, Prop, strings, pairs, the records of Oracle.v) may have any short name the scheme doesn't reserve.
MODEL_KINDS = set().union(*SCHEME.values()) - {'bool', 'list*'}


def kind(ty):
    t = re.sub(r'\b[A-Z]\w*\.', '', ty).replace(' ', '')
    if '->' in t:
        return 'fn->Prop' if t.endswith('Prop') else ('fn->bool' if t.endswith('bool') else 'fn')
    return t


def binders(statement):
    for m in re.finditer(r'\b(forall|exists|fun)\s+', statement):
        i = start = m.end()
        depth = 0
        while i < len(statement):
            ch = statement[i]
            if ch in '({[':
                depth += 1
            elif ch in ')}]':
                depth -= 1
            elif depth == 0 and (statement.startswith(',', i) or statement.startswith('=>', i)):
                break
            i += 1
        head = statement[start:i]
        groups = re.findall(r'\(([^():]+):\s*((?:[^()]|\([^()]*\))*)\)', head)
        if groups:
            for names, ty in groups:
                for name in names.split():
                    yield name, ty.strip()
        elif ':' in head:
            names, ty = head.split(':', 1)
            for name in names.split():
                yield name, ty.strip()


def base_of(name):
    return re.sub(r"[\d']+$", '', name)


def allowed(name, k, type_variables):
    b = base_of(name)
    if b == '_' or len(b) > 3 or '_' in b or b.startswith('H') or b.startswith('IH') or b == 'E':
        return True
    if '...' in k:
        return True  # a type Rocq printed elided
    if k in type_variables or (k.startswith('list') and k[4:] in type_variables):
        return True  # the elements of a polymorphic lemma, and lists of them
    if k.startswith('list') and b == 'l':
        return True
    if k in SCHEME.get(b, ()):
        return True
    if len(b) == 2 and b[0] in CONCEPTS and b[1] in ROLES:
        return k in SCHEME[b[0]]
    return b not in SCHEME and k not in MODEL_KINDS and not (k.startswith('list') and k[4:] in MODEL_KINDS)


def main():
    text = re.sub(r'\s+', ' ', open(sys.argv[1], encoding='utf-8').read())
    violations = collections.Counter()
    examples = {}
    statements = 0
    for module in re.split(r'(?=Module \w+ := Struct )', text):
        header = re.match(r'Module (\w+) := Struct ', module)
        if not header:
            continue
        for entry in re.finditer(r'Parameter (\S+) : (.*?)\. (?=(?:Parameter|Definition|Inductive|Record|Module|Section|Fixpoint|End|Instance|Axiom|Ltac|Notation|CoFixpoint)\b|$)', module):
            statements += 1
            bs = list(binders(entry.group(2)))
            type_variables = {n for n, ty in bs if kind(ty) in ('Type', 'Set')}
            for name, ty in bs:
                k = kind(ty)
                if not allowed(name, k, type_variables):
                    key = (header.group(1), base_of(name), k)
                    violations[key] += 1
                    examples.setdefault(key, entry.group(1))
    total = sum(violations.values())
    if total == 0:
        print(f'> binder names: all {statements} statements follow the scheme')
        return 0
    print(f'> binder names: {total} binders in {statements} statements break the scheme (readme, "Names of binders"):')
    for (module, b, k), count in sorted(violations.items()):
        print(f'    {module}.{examples[(module, b, k)]}: {b} : {k}' + (f' ({count} binders)' if count > 1 else ''))
    return 0 if '--report' in sys.argv else 1


sys.exit(main())
