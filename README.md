# MaxSAT Prover

MaxSAT Prover is an experimental certificate generator for the difficult
`(3,2)`-literal case in an exact MaxSAT branching analysis. The C++ program
enumerates finite CNF templates, tries assignment, grouping, and reduction
strategies, computes their branching vectors, and writes a proof log. A
separate Python verifier checks the assembled certificate using exact rational
branching arithmetic and exhaustive semantic checks of the local transitions.

The current certificate targets the branching base `1.2872`. It is a local
result and still contains named branching-lemma assumptions, so successful
verification is reported as *accepted relative to assumptions*.

## Requirements

- A C++17 compiler (the Makefile uses `g++`)
- GNU Make
- Python 3
- NumPy (`python3 -m pip install numpy`)

## Build

```sh
make
```

This creates the `maxsat_prover` executable in the project root.

## Run

> **Note:** every invocation of `maxsat_prover` recreates
> `pre_certificate.jsonl`. Copy an existing generation log elsewhere before
> running the executable if you need to keep it.

Show the available entry points:

```sh
./maxsat_prover --help
```

Run the interactive template-analysis interface:

```sh
./maxsat_prover test
```

The interface accepts commands such as `add`, `addpos`, `branch`,
`xiao_branch`, `stats`, and `print`; enter `help` for the complete command
list. The included example session can be run non-interactively:

```sh
./maxsat_prover test < solve.txt
```

Some quick internal checks are also available:

```sh
./maxsat_prover reductions
./maxsat_prover groups3
python3 test_verifier.py
```

The C++ generator writes certificate records to `pre_certificate.jsonl`.
After a complete generation session, assemble them into one proof tree with:

```sh
python3 stitch_certificate.py pre_certificate.jsonl proof_tree.json \
  --numerator 12872 --denominator 10000
```

## Verify a certificate

Verify the included certificate independently of the C++ search procedure:

```sh
python3 verify_certificate.py proof_tree.json verification_assumptions
```

On success, the verifier prints certificate statistics and either `ACCEPT` or
`ACCEPT RELATIVE TO ASSUMPTIONS`. The second argument is the output file in
which every remaining named assumption is recorded. 


You can inspect it with, for example:
```sh
python3 -m json.tool verification_assumptions.json
```