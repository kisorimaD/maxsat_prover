import argparse
import json
import sys

from verifier.check import VerificationError, load_and_check


def main():
    parser = argparse.ArgumentParser(description="Check the MaxSAT bottleneck certificate at q=1.2872")
    parser.add_argument("filename", nargs="?", default="proof_tree.json")
    parser.add_argument("assumptions_file", nargs="?", default="verification_assumptions.json")
    parser.add_argument("--local", action="store_true",
                        help="check a local certificate without requiring the paper's root, target and degree family")
    args = parser.parse_args()
    assumptions_file = args.assumptions_file
    try:
        checker = load_and_check(args.filename, bottleneck=not args.local)
    except (OSError, ValueError, TypeError, KeyError, VerificationError) as error:
        print(f"REJECT: {error}", file=sys.stderr)
        return 1
    with open(assumptions_file, "w", encoding="utf-8") as stream:
        json.dump(checker.assumptions, stream, ensure_ascii=False, indent=2)
    verdict = "ACCEPT LOCAL" if args.local else "ACCEPT BOTTLENECK"
    if checker.assumptions:
        verdict += " RELATIVE TO IMPORTED LEMMAS"
    print(f"{verdict}: nodes={checker.nodes}, strategies={checker.strategies}, "
          f"max_depth={checker.max_depth}, assumptions={len(checker.assumptions)}, "
          f"assumption_log={assumptions_file}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
