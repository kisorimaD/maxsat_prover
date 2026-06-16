import json
import itertools
import sys

def canonical_formula(formula):
    # 1. Find all active variables (ids >= 2)
    active_vars = set()
    for clause in formula:
        for lit in clause:
            if abs(lit) >= 2:
                active_vars.add(abs(lit))
                
    sorted_vars = sorted(list(active_vars))
    k = len(sorted_vars)
    
    # 2. Normalize variables to 2, ..., k+1
    var_map = {0: 0, 1: 1} # Keep 0 and 1 fixed
    for idx, v in enumerate(sorted_vars):
        var_map[v] = idx + 2
        
    normalized_formula = []
    for clause in formula:
        normalized_clause = set()
        for lit in clause:
            sign = -1 if lit < 0 else 1
            abs_lit = abs(lit)
            normalized_clause.add(sign * var_map[abs_lit])
        normalized_formula.append(normalized_clause)
        
    # 3. Try all permutations of 1, ..., k+1 to find the lexicographically largest representation string
    best_representation = None
    vars_to_permute = list(range(1, k + 2))
    
    for perm in itertools.permutations(vars_to_permute):
        mapping = {0: 0}
        for idx, val in enumerate(perm):
            mapping[idx + 1] = val
            
        mapped_clauses = []
        for clause in normalized_formula:
            formatted_lits = []
            for lit in clause:
                sign = -1 if lit < 0 else 1
                abs_lit = abs(lit)
                mapped_id = mapping[abs_lit]
                inv = (sign == -1)
                formatted_lits.append(("~" if inv else "=") + str(mapped_id))
            formatted_lits.sort()
            clause_str = "(" + "∨".join(formatted_lits) + ")"
            mapped_clauses.append(clause_str)
            
        mapped_clauses.sort()
        formula_str = "∧".join(mapped_clauses)
        
        if best_representation is None or formula_str > best_representation:
            best_representation = formula_str
            
    return best_representation

def build_formula(formula, assignment, v, i, j, lit_type):
    new_formula = []
    pos_placed = 0
    neg_placed = 0
    for clause, role in zip(formula, assignment):
        new_clause = set(clause)
        if role == '+':
            if 1 in new_clause:
                new_clause.remove(1)
                new_clause.add(0)
            new_clause.add(v)
            pos_placed += 1
        elif role == '-':
            if 1 in new_clause:
                new_clause.remove(1)
                new_clause.add(0)
            new_clause.add(-v)
            neg_placed += 1
        new_formula.append(new_clause)
        
    for _ in range(i - pos_placed):
        new_formula.append({0, v})
        
    for _ in range(j - neg_placed):
        if lit_type == 'SINGLETON':
            new_formula.append({-v})
        else:
            new_formula.append({0, -v})
            
    return new_formula

def generate_formulas_universal(formula, v, i, j, lit_type, pos=-1, only_pos=False):
    n = len(formula)
    wildcard_indices = [idx for idx, clause in enumerate(formula) if 0 in clause or 1 in clause]
    w = len(wildcard_indices)
    
    generated = []
    for roles in itertools.product(['+', '-', None], repeat=w):
        assignment = [None] * n
        for idx, role in zip(wildcard_indices, roles):
            assignment[idx] = role
            
        if only_pos and assignment[pos] != '+':
            continue
            
        pos_placed = sum(1 for role in assignment if role == '+')
        neg_placed = sum(1 for role in assignment if role == '-')
        
        if pos_placed > i or neg_placed > j:
            continue
            
        if lit_type == 'SINGLETON' and neg_placed > 0:
            continue
            
        res = build_formula(formula, assignment, v, i, j, lit_type)
        generated.append(res)
        
    return generated

# Global counters
stats = {"add_variable": 0, "addpos": 0, "divide_clause": 0}

POSSIBLE_LITERALS = [
    (1, 3, 'SINGLETON'),
    (3, 1, 'SINGLETON'),
    (2, 2, 'ANY'),
    (3, 2, 'ANY'),
    (2, 3, 'ANY'),
    (1, 4, 'SINGLETON'),
    (4, 1, 'SINGLETON')
]

def modify_clause(formula, pos, remove_val, add_val=None):
    new_formula = [set(c) for c in formula]
    if pos < len(new_formula) and remove_val in new_formula[pos]:
        new_formula[pos].remove(remove_val)
        if add_val is not None:
            new_formula[pos].add(add_val)
    return new_formula

def verify_node(node):
    node_id = node.get("node_id")
    node_type = node.get("type")
    
    if node_type == "add_variable":
        formula = node.get("formula", [])
        v = node.get("added_variable_id")
        i = node.get("pos_deg")
        j = node.get("neg_deg")
        lit_type = 'SINGLETON' if (i == 1 or j == 1) else 'ANY'
        
        generated = generate_formulas_universal(formula, v, i, j, lit_type)
        gen_canon = {canonical_formula(f) for f in generated}
        child_canon = {canonical_formula(c["formula"]) for c in node.get("children", [])}
        
        # Verify that all child formulas are isomorphic to one of the generated ones
        missing = child_canon - gen_canon
        uncovered = gen_canon - child_canon
        if missing or uncovered:
            print(f"ERROR: Node {node_id} (type: add_variable) formula sets do not match!")
            print(f"Parent formula: {formula}")
            print(f"Variable to add: {v}, deg: ({i}, {j}), type: {lit_type}")
            if missing:
                print("Invalid child canonical forms (not generated by transition):")
                for m in list(missing)[:5]:
                    print(m)
            if uncovered:
                print("Missing/uncovered canonical forms (generated but not found in children):")
                for u in list(uncovered)[:5]:
                    print(u)
            sys.exit(1)
            
        stats["add_variable"] += 1
        
    elif node_type == "addpos":
        formula = node.get("formula", [])
        v = node.get("added_variable_id")
        pos = node.get("target_clause_idx")
        
        generated_addpos = []
        # 1. Variants
        for vi, vj, vtype in POSSIBLE_LITERALS:
            generated_addpos.extend(generate_formulas_universal(formula, v, vi, vj, vtype, pos=pos, only_pos=True))
        # 2. Empty space
        cnf_empty_space = modify_clause(formula, pos, 0)
        generated_addpos.append(cnf_empty_space)
        
        gen_canon = {canonical_formula(f) for f in generated_addpos}
        child_canon = {canonical_formula(c["formula"]) for c in node.get("children", [])}
        
        missing = child_canon - gen_canon
        uncovered = gen_canon - child_canon
        if missing or uncovered:
            print(f"ERROR: Node {node_id} (type: addpos) formula sets do not match!")
            print(f"Parent formula: {formula}")
            print(f"Variable to add: {v}, target clause index: {pos}")
            if missing:
                print("Invalid child canonical forms (not generated by transition):")
                for m in list(missing)[:5]:
                    print(m)
            if uncovered:
                print("Missing/uncovered canonical forms (generated but not found in children):")
                for u in list(uncovered)[:5]:
                    print(u)
            sys.exit(1)
            
        stats["addpos"] += 1
        
    elif node_type == "divide_clause":
        formula = node.get("formula", [])
        pos = node.get("target_clause_idx")
        
        # We expect exactly 2 children
        children = node.get("children", [])
        if len(children) != 2:
            print(f"ERROR: Node {node_id} (type: divide_clause) has {len(children)} children instead of 2!")
            sys.exit(1)
            
        # Expected outputs
        cnf_empty = modify_clause(formula, pos, 0)
        cnf_not_empty = modify_clause(formula, pos, 0, 1)
            
        expected_empty_canon = canonical_formula(cnf_empty)
        expected_not_empty_canon = canonical_formula(cnf_not_empty)
        
        child0_canon = canonical_formula(children[0]["formula"])
        child1_canon = canonical_formula(children[1]["formula"])
        
        if child0_canon != expected_empty_canon:
            print(f"ERROR: Node {node_id} (type: divide_clause) child 0 does not match empty branch!")
            print(f"Parent: {formula}")
            print(f"Expected empty: {cnf_empty}")
            print(f"Expected empty (canon): {expected_empty_canon}")
            print(f"Child 0: {children[0]['formula']}")
            print(f"Child 0 (canon): {child0_canon}")
            sys.exit(1)
            
        if child1_canon != expected_not_empty_canon:
            print(f"ERROR: Node {node_id} (type: divide_clause) child 1 does not match not_empty branch!")
            print(f"Parent: {formula}")
            print(f"Expected not_empty: {cnf_not_empty}")
            print(f"Expected not_empty (canon): {expected_not_empty_canon}")
            print(f"Child 1: {children[1]['formula']}")
            print(f"Child 1 (canon): {child1_canon}")
            sys.exit(1)
            
        stats["divide_clause"] += 1

    # Recurse on children
    for child in node.get("children", []):
        verify_node(child)

def main():
    filename = sys.argv[1] if len(sys.argv) > 1 else "proof_tree.json"
    print(f"Loading {filename}...")
    with open(filename, "r") as f:
        data = json.load(f)
        
    proof_tree = data["proof_tree"]
    print(f"Loaded proof tree with {len(proof_tree)} roots.")
    
    for idx, root in enumerate(proof_tree):
        print(f"Verifying root {idx+1}...")
        verify_node(root)
        
    print("\n--------------------------------------------------")
    print("Topological verification completed successfully!")
    print("Verified transition counts:")
    for k, v in stats.items():
        print(f"  - {k}: {v}")
    print("--------------------------------------------------")

if __name__ == "__main__":
    main()
