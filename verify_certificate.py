import argparse
import json
import sys
from collections import Counter

from verifier.check import VerificationError, load_and_check


def main():
    parser = argparse.ArgumentParser(description="Check a local MaxSAT certificate")
    parser.add_argument("filename", nargs="?", default="proof_tree.json")
    parser.add_argument("assumptions_file", nargs="?", default="verification_assumptions.json")
    args = parser.parse_args()
    assumptions_file = args.assumptions_file
    try:
        checker = load_and_check(args.filename)
    except (OSError, ValueError, TypeError, KeyError, VerificationError) as error:
        print(f"REJECT: {error}", file=sys.stderr)
        return 1
    with open(assumptions_file, "w", encoding="utf-8") as stream:
        json.dump(checker.assumptions, stream, ensure_ascii=False, indent=2)
    verdict = "ACCEPT LOCAL"
    if checker.assumptions:
        verdict += " RELATIVE TO IMPORTED LEMMAS"
    print(verdict)
    print(f"root={json.dumps(checker.root)}")
    print(f"q={checker.target}, possible_degrees={json.dumps(sorted(checker.possible_degrees))}")
    imports = Counter(item["name"] for item in checker.assumptions)
    print(f"nodes={checker.nodes}, strategies={checker.strategies}, max_depth={checker.max_depth}")
    print(f"imports={len(checker.assumptions)} {json.dumps(imports, sort_keys=True)}, "
          f"assumption_log={assumptions_file}")
    print(f"max_weight={checker.max_weight} (~{float(checker.max_weight):.12f})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
