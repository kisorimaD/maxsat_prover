import argparse
import json
import sys


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

    certificate = {
        "format": "maxsat-local-proof-v1",
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
