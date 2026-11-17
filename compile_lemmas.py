"""Validate saved proof artifacts once and emit a small native search index.

The index is an internal startup protocol, not an independently trusted proof.
Search never invokes Python; assembly verifies the original artifacts again.
"""
import json
import math
from fractions import Fraction
from pathlib import Path
import sys

from lemma_library import definition_digest, validate_saved_lemma, step6_context_mask
from verifier.formula import is_tail, ordered_formula


def decimal_target_key(target):
    q = Fraction(target['numerator'], target['denominator'])
    denominator = q.denominator
    powers = []
    for base in (2, 5):
        count = 0
        while denominator % base == 0:
            denominator //= base
            count += 1
        powers.append(count)
    if denominator != 1:
        return f'rational:{q.numerator}/{q.denominator}'
    scale = max(powers)
    digits = str(q.numerator * 2 ** (scale - powers[0]) * 5 ** (scale - powers[1]))
    exponent = -scale
    while digits.endswith('0'):
        digits = digits[:-1]
        exponent += 1
    return f'{digits}e{exponent}'


def compile_definition(path):
    path = Path(path).resolve()
    definition = json.loads(path.read_text())
    validate_saved_lemma(definition)
    context_mask = step6_context_mask(definition)
    roles = definition['roles']
    if not 1 <= len(roles) <= 30:
        raise ValueError('native lemma matching needs between 1 and 30 root roles')
    role_index = {var: index + 1 for index, var in enumerate(roles)}
    clauses = []
    seen_tails = set()
    for clause in ordered_formula(definition['proof']['formula']):
        tails = [lit for lit in clause if is_tail(lit)]
        literals = [role_index[abs(lit)] * (1 if lit > 0 else -1)
                    for lit in clause if type(lit) is int]
        if not literals or len(tails) > 1 or any(lit[1] in seen_tails for lit in tails):
            raise ValueError('native lemma roots need incident clauses with distinct single tails')
        seen_tails.update(lit[1] for lit in tails)
        clauses.append((-1 if not tails else int(tails[0][2] == 'nonempty'), literals))
    q = float(Fraction(**definition['target']))
    if not math.isfinite(q) or q <= 1:
        raise ValueError('lemma target is outside the native search numeric range')
    hex_text = lambda value: value.encode('utf-8').hex()
    lines = [hex_text(definition['id']), definition_digest(definition), hex_text(str(path)),
             hex_text(decimal_target_key(definition['target'])), repr(q),
             str(int(bool(definition['premises']['imports']))), str(context_mask)]
    families = [premise['degrees'] for premise in definition['premises']['degrees']]
    lines.append(str(len(families)))
    for family in families:
        lines.append(str(len(family)))
        lines += [f'{p} {n} {int(s)}' for p, n, s in family]
    lines.append(str(len(roles)))
    lines.append(str(len(definition['vector'])) + ' ' + ' '.join(map(str, definition['vector'])))
    lines.append(str(len(clauses)))
    lines += [f'{tail} {len(literals)} ' + ' '.join(map(str, literals))
              for tail, literals in clauses]
    return definition['id'], '\n'.join(lines)


def main():
    try:
        entries = [compile_definition(path) for path in sys.argv[1:]]
        if len({name for name, _ in entries}) != len(entries):
            raise ValueError('duplicate saved lemma identifiers')
        print('maxsat-lemma-index-v2')
        print(len(entries))
        for _, index in entries:
            print(index)
    except Exception as error:
        # A failed proof check must leave the generator's current log intact.
        print(f'lemma loading failed: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
