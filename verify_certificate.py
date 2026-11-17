import argparse
import json
import sys

from verifier.check import VerificationError, load_and_check


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('filename',nargs='?',default='proof_tree.json')
    parser.add_argument('imported_lemmas_file',nargs='?',default='imported_lemmas.json')
    parser.add_argument('--allow-restarts',action='store_true',help='check a local induction step requiring a complete global solver')
    args=parser.parse_args()
    filename,imported_lemmas_file=args.filename,args.imported_lemmas_file
    try:
        checker = load_and_check(filename,allow_restarts=args.allow_restarts)
    except (OSError, ValueError, TypeError, KeyError, VerificationError) as error:
        print(f"REJECT: {error}", file=sys.stderr)
        return 1
    with open(imported_lemmas_file, "w", encoding="utf-8") as stream:
        json.dump(checker.assumptions, stream, ensure_ascii=False, indent=2)
    if checker.restart_obligations:
        verdict = "ACCEPT LOCAL INDUCTION STEP" + (" RELATIVE TO IMPORTED LEMMAS" if checker.assumptions else "")
    elif checker.assumptions:
        verdict = "ACCEPT RELATIVE TO IMPORTED LEMMAS"
    elif (getattr(checker,"maximum_clause_size",-1) != -1 or
          getattr(checker,"maximum_variable_occurrences",-1) != -1):
        verdict = "ACCEPT LOCAL"
    else:
        verdict = "ACCEPT"
    print(f"{verdict}: nodes={checker.nodes}, strategies={checker.strategies}, "
          f"max_depth={checker.max_depth}, "
          f"imported_lemmas={len(checker.assumptions)}, "
          f"restart_obligations={len(checker.restart_obligations)}, "
          f"imported_lemmas_log={imported_lemmas_file}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
