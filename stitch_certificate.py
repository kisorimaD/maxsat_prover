import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from lemma_library import (PROOF_FILES, expand_lemma_applications,
                           save_session_lemma, validate_saved_lemma, definition_digest)
from verifier.arithmetic import target_fraction
from verifier.check import VerificationError


def assemble_certificate(input_file, output_file, numerator=None, denominator=None,
                         lemma_files=()):
    nodes = {}
    referenced = set()

    with open(input_file, "r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(f"invalid JSON at line {line_number}: {error}") from error
            if record.get("kind") == "rollback":
                if set(record)!={"kind","parent_ids"} or not isinstance(record['parent_ids'],list) or not record['parent_ids']:
                    raise ValueError("invalid rollback record")
                ids=record['parent_ids']
                if any(type(i) is not int for i in ids) or len(set(ids))!=len(ids):
                    raise ValueError("invalid rollback parent IDs")
                parents={str(i) for i in ids}
                if any(i not in nodes or nodes[i].get('kind')!='refine' for i in parents):
                    raise ValueError("rollback requires existing refinement parents")
                discarded=set()
                def collect(i):
                    if i in discarded:return
                    discarded.add(i)
                    for child in nodes.get(i,{}).get('children_ids',[]):collect(str(child))
                for i in parents:collect(i)
                # A child can be shared by another, still-active refinement.
                # Keep its complete subtree; only the selected parent records
                # must be replaced by the next tactic.
                protected=set()
                def protect(i):
                    if i in protected or i in parents:return
                    protected.add(i)
                    for child in nodes.get(i,{}).get('children_ids',[]):protect(str(child))
                for i,node in nodes.items():
                    if i not in discarded:
                        for child in node.get('children_ids',[]):
                            if str(child) in discarded:protect(str(child))
                for i in discarded-protected:nodes.pop(i,None)
                continue
            node_id = str(record.pop("node_id"))
            if node_id in nodes:
                raise ValueError(f"duplicate node_id {node_id}")
            nodes[node_id] = record
            referenced.update(str(value) for value in record.get("children_ids", []))

    referenced={str(child) for node in nodes.values() for child in node.get("children_ids",[])}
    roots = set(nodes) - referenced
    if len(roots) != 1:
        raise ValueError(f"expected exactly one root, found {sorted(roots)}")

    visiting = set()
    built = set()

    def build(node_id):
        if node_id not in nodes:
            raise ValueError(f"missing referenced node {node_id}")
        if node_id in visiting:
            raise ValueError(f"cycle through node {node_id}")
        visiting.add(node_id)
        node = dict(nodes[node_id])
        child_ids = node.pop("children_ids", None)
        if child_ids is not None:
            node["children"] = [build(str(child)) for child in child_ids]
        visiting.remove(node_id)
        built.add(node_id)
        return node

    root_id = next(iter(roots))
    root = build(root_id)
    if built != set(nodes):
        raise ValueError(f"unreachable nodes: {sorted(set(nodes) - built)}")

    export = root.pop("lemma_export", None)
    lemma_sources = root.pop("lemma_sources", [])
    if not isinstance(lemma_sources, list):
        raise ValueError("invalid saved lemma sources")
    if export is not None:
        if (not isinstance(export, dict) or set(export) != {"q", "output"} or
                not isinstance(export["q"], str) or
                not isinstance(export["output"], str) or not export["output"]):
            raise ValueError("invalid lemma export settings")
        q = Fraction(export["q"])
        target_fraction(q.numerator, q.denominator)
        if ((numerator is not None or denominator is not None) and
                target_fraction(numerator if numerator is not None else 12872,
                                denominator if denominator is not None else 10000) != q):
            raise ValueError("assembly target differs from the fixed lemma-session target")
        numerator, denominator = q.numerator, q.denominator
        if Path(export["output"]).resolve() in {
                Path(input_file).resolve(), Path(output_file).resolve()}:
            raise ValueError("lemma output must differ from the log and certificate files")
    numerator = 12872 if numerator is None else numerator
    denominator = 10000 if denominator is None else denominator
    target = {"numerator": numerator, "denominator": denominator}
    target_fraction(**target)

    maximum_clause_size = root.pop("maximum_clause_size", None)
    maximum_variable_occurrences = root.pop(
        "maximum_variable_occurrences", None)
    if root.get("kind") == "root_family":
        from verifier.refine import declared_root
        if maximum_variable_occurrences is not None:
            from verifier.formula import (validate_maximum_clause_size,
                                          validate_maximum_variable_occurrences)
            if maximum_clause_size is None:
                maximum_clause_size = -1
            validate_maximum_clause_size(maximum_clause_size)
            validate_maximum_variable_occurrences(
                maximum_variable_occurrences)
            certificate_format = "maxsat-local-proof-v4"
        elif maximum_clause_size is None:
            # Logs produced before v3 describe unrestricted MaxSAT.
            maximum_clause_size = -1
            maximum_variable_occurrences = -1
            certificate_format = "maxsat-local-proof-v2"
        else:
            from verifier.formula import validate_maximum_clause_size
            validate_maximum_clause_size(maximum_clause_size)
            maximum_variable_occurrences = -1
            certificate_format = "maxsat-local-proof-v3"
        if certificate_format == "maxsat-local-proof-v2":
            root = declared_root(root)
        else:
            root = declared_root(
                root, maximum_clause_size=maximum_clause_size,
                maximum_variable_occurrences=maximum_variable_occurrences)
    else:
        if (maximum_clause_size is not None or
                maximum_variable_occurrences is not None):
            raise ValueError("constraint metadata is only valid on root_family")
        maximum_clause_size = -1
        maximum_variable_occurrences = -1
        certificate_format = "maxsat-local-proof-v2"

    definitions = {name: json.loads(path.read_text()) for name, path in PROOF_FILES.items()}
    for path in lemma_files:
        definition = json.loads(Path(path).read_text())
        validate_saved_lemma(definition)
        if definition["id"] in definitions:
            raise ValueError(f"duplicate lemma definition {definition['id']!r}")
        definitions[definition["id"]] = definition
    source_ids = set()
    for source in lemma_sources:
        if (not isinstance(source, dict) or set(source) != {"id", "digest", "path"} or
                any(not isinstance(source[field], str) or not source[field] for field in source)):
            raise ValueError("invalid saved lemma source")
        if source['id'] in source_ids:
            raise ValueError("duplicate saved lemma source")
        source_ids.add(source['id'])
        if source['id'] in definitions:
            definition = definitions[source['id']]
        else:
            definition = json.loads(Path(source['path']).read_text())
            validate_saved_lemma(definition)
            definitions[definition['id']] = definition
        if definition['id'] != source['id'] or definition_digest(definition) != source['digest']:
            raise ValueError("saved lemma definition changed since generation")
    root = expand_lemma_applications(root, definitions, target=target)
    certificate = {
        "format": certificate_format,
        "target": target,
        "proof": root,
    }
    if certificate_format == "maxsat-local-proof-v3":
        certificate["maximum_clause_size"] = maximum_clause_size
        certificate["scope"] = {
            "kind": "local_template_family",
            "degree_coverage": "certificate_premise",
        }
    elif certificate_format == "maxsat-local-proof-v4":
        certificate["maximum_clause_size"] = maximum_clause_size
        certificate["maximum_variable_occurrences"] = \
            maximum_variable_occurrences
        certificate["scope"] = {
            "kind": "local_template_family",
            "degree_coverage": "certificate_premise",
        }
    if export is not None:
        if certificate_format != "maxsat-local-proof-v2":
            raise ValueError("lemma export currently requires an unrestricted v2 session")
        definition = save_session_lemma(root, export["output"], target)
        print(f"Saved lemma {definition['id']}: q={numerator}/{denominator}, "
              f"worst vector={definition['vector']}, "
              f"imported lemmas={len(definition['premises']['imports'])}")
    with open(output_file, "w", encoding="utf-8") as stream:
        json.dump(certificate, stream, separators=(",", ":"), allow_nan=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", nargs="?", default="pre_certificate.jsonl")
    parser.add_argument("output", nargs="?", default="proof_tree.json")
    parser.add_argument("--numerator", type=int)
    parser.add_argument("--denominator", type=int)
    parser.add_argument("--lemma", action="append", default=[], metavar="FILE",
                        help="load a saved fixed-q lemma for application expansion")
    args = parser.parse_args()
    try:
        assemble_certificate(args.input, args.output,
                             args.numerator, args.denominator, args.lemma)
    except (OSError, ValueError, KeyError, TypeError, VerificationError) as error:
        print(f"certificate assembly failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
