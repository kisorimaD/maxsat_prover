from collections import defaultdict

from .formula import is_tail


IMPORTS = {}


def imported_lemma(name):
    def register(check):
        IMPORTS[name] = check
        return check
    return register


def literal_occurrences(formula):
    occurrences = defaultdict(set)
    for index, clause in enumerate(formula):
        for literal in clause:
            if type(literal) is int:
                occurrences[literal].add(index)
    return dict(occurrences)


def unit_count(formula, indices, literal):
    return sum(formula[index] == (literal,) for index in indices)


def remainder_size(clause, literal):
    variables = {abs(item) for item in clause if type(item) is int} - {abs(literal)}
    return len(variables) + any(is_tail(item) and item[2] == "nonempty" for item in clause)


def minority_clauses(formula, occurrences):
    for literal, positive in occurrences.items():
        negative = occurrences.get(-literal, ())
        if len(negative) == 1 and positive.isdisjoint(negative):
            yield literal, len(positive), formula[next(iter(negative))]


@imported_lemma("lemma2")
def lemma2(formula, occurrences):
    for literal, i, minority in minority_clauses(formula, occurrences):
        size = remainder_size(minority, literal)
        if size >= 1:
            vector = (i, 1 + 2 * size)
            yield [literal], vector, (vector, (1,))


@imported_lemma("lemma3")
def lemma3(formula, occurrences):
    for literal, i, minority in minority_clauses(formula, occurrences):
        if i == 2:
            vector = (1, max(8, 7 + 2 * remainder_size(minority, literal)))
            yield [literal], vector, (vector, (1,))


@imported_lemma("lemma4")
def lemma4(formula, occurrences):
    for literal, positive in occurrences.items():
        negative = occurrences.get(-literal, ())
        i, j = len(positive), len(negative)
        if i >= j >= 2 and positive.isdisjoint(negative):
            units = unit_count(formula, positive, literal)
            vector = (i, 2 * j + 1)
            if units >= j:
                # R-Rule 3 satisfies at least the i clauses containing literal.
                yield [literal], vector, ((i,),)
            elif units == j - 1:
                yield [literal], vector, (vector, (1,))


@imported_lemma("double_lemma3")
def double_lemma3(formula, occurrences):
    singletons = [literal for literal, i, minority in minority_clauses(formula, occurrences)
                  if i == 2 and minority == (-literal,)]
    if len(singletons) >= 2:
        vector = (8, 9, 2)
        yield singletons[:2], vector, (vector, (1,), (8, 2))
