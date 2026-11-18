# MaxSAT Prover

A certificate generator for the `(3,2)`-literal bottleneck in the MaxSAT
branching analysis described in `.docs/main.pdf`. The C++ search enumerates
local templates, enumerates assignments, and searches for groups with cheap
continuations on their residual formulas.
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

## Verification contract

By default the verifier requires the paper's profile:

- target `1.2872` (exactly `1609/1250`);
- root `(x∨?1)(x∨?2)(x∨?3)(¬x∨?4)(¬x∨?5)`, up to renaming;
- exposure classes `(3,1)-singleton`, `(2,2)`, `(3,2)`, `(2,3)`,
  `(4,1)-singleton`.

It checks all refinement children, both sides of assignments, semantic
decompositions for every boundary valuation, clause decreases and the final
branching vectors. Step 5.1 is expanded into an ordinary assignment proof,
including both residual formulas; it is not an imported assumption.

Only `lemma2`, `lemma3`, `lemma4` and `double_lemma3` are allowed as imports.
These refer to the baseline results identified in the paper, not to lemmas
of the same numbers in this project's paper. Every imported occurrence is
written to `verification_assumptions.json`, with its formula, vector and path.
The successful result is `ACCEPT BOTTLENECK RELATIVE TO IMPORTED LEMMAS`.

The checker uses the larger weight of the logged branching case and a
one-clause reduction. It relies on the source lemmas and their applicability,
including the baseline algorithm's global structural restrictions. The
completeness of the five exposure classes for Step 5.4 is the
argument in §5.2 of the paper. An accepted certificate is a local analysis
relative to these premises, not an independently verified complete MaxSAT solver.

For another local family or target, opt out of the paper's profile explicitly:

```sh
python3 verify_certificate.py local_proof.json local_assumptions.json --local
```

This reports `ACCEPT LOCAL`, with the same qualification if imports remain.
Only certificate format `maxsat-local-proof-v2` and explicitly typed tails
are supported. Old v1 certificates and numeric tail shorthands must be regenerated.

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
