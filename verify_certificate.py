import json
import sys

from verifier.check import VerificationError, load_and_check


def main():
    filename = sys.argv[1] if len(sys.argv) >= 2 else "proof_tree.json"
    assumptions_file = (sys.argv[2] if len(sys.argv) >= 3
                        else "verification_assumptions.json")
    try:
        checker = load_and_check(filename)
    except (OSError, ValueError, TypeError, KeyError, VerificationError) as error:
        print(f"REJECT: {error}", file=sys.stderr)
        return 1
    with open(assumptions_file, "w", encoding="utf-8") as stream:
        json.dump(checker.assumptions, stream, ensure_ascii=False, indent=2)
    verdict = "ACCEPT RELATIVE TO ASSUMPTIONS" if checker.assumptions else "ACCEPT"
    print(f"{verdict}: nodes={checker.nodes}, strategies={checker.strategies}, "
          f"max_depth={checker.max_depth}, assumptions={len(checker.assumptions)}, "
          f"assumption_log={assumptions_file}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
