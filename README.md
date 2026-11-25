# MaxSAT Prover

A certificate generator for the `(3,2)`-literal bottleneck in the MaxSAT
branching analysis. The C++ generator enumerates local templates and assignments, then searches for
groups with low-cost continuations on their residual formulas.
An independent Python checker validates coverage, local optimum identities
and the branching inequality using exact rational arithmetic.

## Requirements

- A C++17 compiler (`g++` by default) and GNU Make
- Python 3 with NumPy (`python3 -m pip install numpy`)

## Reproduce the bottleneck result

```sh
make certificate
```

This builds the generator, runs `solve.txt`, assembles `proof_tree.json`, and
checks it at `q = 1.2872`. Generation must leave zero unresolved cases; an
incomplete proof log is rejected during assembly. Generated artifacts are
ignored by Git. The steps can also be run separately:

```sh
make
./maxsat_prover interactive < solve.txt
python3 stitch_certificate.py pre_certificate.jsonl proof_tree.json
python3 verify_certificate.py proof_tree.json verification_assumptions.json
```

Starting `maxsat_prover interactive` overwrites `pre_certificate.jsonl`. The
test suite and `--help` preserve it. `make certificate`
also overwrites the assembled certificate and assumption log.

### How `solve.txt` works

Each refinement replaces selected unresolved
templates with their cases. Each search records the strategies that meet the
target and removes those templates from the set. [`solve.txt`](solve.txt)

| Lines | Command | What it does |
| --- | --- | --- |
| 1 | `set 1.2872` | Set the branching target `q` for strategy search. |
| 3 | `add x 3 2 a` | Start with three clauses containing `x` and two containing `¬x`, each with an arbitrary tail. `a` is shorthand for `ANY`. |
| 4–6 | `addpos y` | Expose `y` from a tail in a clause containing `¬x`. |
| 7 | `branch` | Search for strategies on the remaining templates. Try plain assignment branching first, then grouped branching on the cases still unresolved. |
| 8–10 | `addpos z` | Expose `z` from a tail in a clause containing `¬x` with the positive literal `y` forbidden. |
| 12 | `branch` | Search again after exposing `z`. |
| 13 | `empty_divide -1` | For each remaining template with an arbitrary tail, choose the empty-versus-nonempty split that minimizes the worse child weight. |
| 14 | `branch` | Search the cases left after the tail split. |
| 16 | `exit` | End the generator session. |

Each `addpos` command reads two lines after the variable name. The first lists
required literals and the second lists forbidden literals. `-x` denotes `¬x`,
so the empty line after the first `-x` means the exposure of `y` has no
forbidden literals. For each eligible template, the command uses the first
matching clause and enumerates the allowed degree classes and placements of the
new variable's occurrences.

### Quantities used in the search and certificate

| Code term | Meaning |
| --- | --- |
| `offset` | Additive contribution to the MAX-SAT optimum for a transition, measured in satisfied clauses. |
| `decrease` | Reduction in the clause-count parameter `m` of the recursive instance. A clause that becomes empty can contribute to `decrease` with zero `offset`. |
| `branching_weight` | Weight `W_q(v) = sum(q^(-d) for d in v)` of a vector `v` of accumulated decreases at the fixed target `q`. The target test requires positive decreases and weight at most one. |
| `branching_factor` | For a progressing branching vector, the value at which its weight is one. |

## Verification contract

The verifier reads the root, exact rational `target` and `possible_degrees`
from the certificate. Each exposure must cover the same set of degree classes,
in any order. The assembler takes the list from the first logged exposure and
writes an empty list for certificates without exposures.

The verifier checks all refinement children, both sides of assignments,
semantic decompositions for every boundary valuation, clause decreases and
the final branching weights. Semantic decompositions preserve the provenance
of nonempty tails. Step 5.1 is expanded into an assignment proof with both
residual formulas.

The verifier checks the applicability and claimed branching vector of every
`lemma2`, `lemma3`, `lemma4` and `double_lemma3` import. It uses the worst
weight among the applicable branching and reduction outcomes. The import log
records the formula, vector, path and witness for each import.

An accepted certificate certifies the declared local family, conditional on
the imported mathematical results and the completeness of the declared
classes for the intended algorithm step. The output lists the root, target,
classes, strategy and import counts, and maximum certified weight. To check
another certificate, run:

```sh
python3 verify_certificate.py local_proof.json local_assumptions.json
```

Only certificate format `maxsat-local-proof-v2` and explicitly typed tails
are supported. Regenerate certificates that lack `possible_degrees` or use
numeric tail shorthands.

## Tests and interactive search

```sh
make check
./maxsat_prover --help
./maxsat_prover interactive
```

`make check` runs the separate C++ test executable and Python tests in `tests/`.
`make certificate`
is the separate full experiment. The interactive interface remains available
for diagnostics; `help` lists its commands. Set `assumptions off` to exclude
imported lemmas from search; constructive Step 5.1 remains available. The current
full scenario needs imported lemmas to resolve all cases.
