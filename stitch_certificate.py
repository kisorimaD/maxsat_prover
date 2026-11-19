import argparse
import json
import sys


def _declared_root(node):
    fields = {"kind", "formula", "variable", "positive", "negative",
              "singleton", "children"}
    if set(node) != fields:
        raise ValueError("invalid root family declaration")
    if node["formula"] != [] or len(node["children"]) != 1:
        raise ValueError("root declaration needs an empty seed and exactly one child")

    variable = node["variable"]
    positive, negative, singleton = node["positive"], node["negative"], node["singleton"]
    if type(variable) is not int or variable < 2:
        raise ValueError("root declaration requires an ordinary variable")
    if (type(positive) is not int or type(negative) is not int or
            positive < 1 or negative < 1 or positive + negative > 30 or
            type(singleton) is not bool):
        raise ValueError("invalid root degrees")
    if singleton and negative != 1:
        raise ValueError("singleton requires negative degree 1")

    child = node["children"][0]
    formula = child["formula"]
    if not isinstance(formula, list) or len(formula) != positive + negative:
        raise ValueError("root family differs from its declared degrees")

    # The child may rename the declared variable and reorder its clauses.
    variables = set()
    tails = set()
    positive_count = 0
    for clause in formula:
        if not isinstance(clause, list):
            raise ValueError("root clause must be a list")
        literals = [literal for literal in clause if type(literal) is int]
        if len(literals) != 1 or abs(literals[0]) < 2:
            raise ValueError("root clause requires one ordinary literal")

        literal = literals[0]
        variables.add(abs(literal))
        positive_count += literal > 0
        if literal < 0 and singleton and len(clause) == 1:
            continue
        if (literal < 0 and singleton) or len(clause) != 2:
            raise ValueError("invalid root clause size")

        tail = next(item for item in clause if type(item) is not int)
        if (not isinstance(tail, dict) or set(tail) != {"tail", "kind"} or
                type(tail["tail"]) is not int or tail["kind"] != "any" or
                tail["tail"] in tails):
            raise ValueError("root clause requires a distinct arbitrary tail")
        tails.add(tail["tail"])

    if len(variables) != 1 or positive_count != positive:
        raise ValueError("root family differs from its declared degrees")
    return child


def assemble_certificate(input_file, output_file, numerator=12872, denominator=10000):
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
            node_id = str(record.pop("node_id"))
            if node_id in nodes:
                raise ValueError(f"duplicate node_id {node_id}")
            nodes[node_id] = record
            referenced.update(str(value) for value in record.get("children_ids", []))

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

    if root.get("kind") == "root_family":
        root = _declared_root(root)

    certificate = {
        "format": "maxsat-local-proof-v2",
        "target": {"numerator": numerator, "denominator": denominator},
        "proof": root,
    }
    with open(output_file, "w", encoding="utf-8") as stream:
        json.dump(certificate, stream, separators=(",", ":"), allow_nan=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", nargs="?", default="pre_certificate.jsonl")
    parser.add_argument("output", nargs="?", default="proof_tree.json")
    parser.add_argument("--numerator", type=int, default=12872)
    parser.add_argument("--denominator", type=int, default=10000)
    args = parser.parse_args()
    try:
        assemble_certificate(args.input, args.output,
                             args.numerator, args.denominator)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"certificate assembly failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
