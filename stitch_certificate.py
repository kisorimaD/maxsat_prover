import json
import sys

def assemble_certificate(input_file, output_file):
    nodes = {}
    all_children = set()

    print(f"Читаю плоский лог {input_file}...")
    
    # Шаг 1: Индексация всех узлов
    with open(input_file, 'r', encoding='utf-8') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            
            try:
                record = json.loads(line)
                parent_id = str(record["parent_id"])

                if record["type"] == "add_variable":  # Исправлено с "macro_add_variable"
                    nodes[parent_id] = {
                        "node_id": parent_id,
                        "type": "add_variable",
                        "formula": record["formula"],
                        "added_variable_id": record.get("added_variable_id", 0),
                        # Берем реальные значения из лога вместо хардкода
                        "pos_deg": record.get("pos_deg", 3), 
                        "neg_deg": record.get("neg_deg", 2), 
                        "children_ids": [str(c) for c in record["children_ids"]]
                    }
                    all_children.update(nodes[parent_id]["children_ids"])

                elif record["type"] == "addpos":  # Добавлен парсинг для addpos
                    nodes[parent_id] = {
                        "node_id": parent_id,
                        "type": "addpos",
                        "formula": record["formula"],
                        "added_variable_id": record.get("added_variable_id", 0),
                        "target_clause_idx": record["target_clause_idx"],
                        "children_ids": [str(c) for c in record["children_ids"]]
                    }
                    all_children.update(nodes[parent_id]["children_ids"])
                    
                elif record["type"] == "macro_divide_clause":
                    nodes[parent_id] = {
                        "node_id": parent_id,
                        "type": "divide_clause",
                        "formula": record["formula"],
                        "target_clause_idx": record["target_clause_idx"],
                        "children_ids": [str(c) for c in record["children_ids"]]
                    }
                    all_children.update(nodes[parent_id]["children_ids"])

                elif record["type"] == "proof_tree":
                    # Это уже готовое микро-дерево
                    proof_node = record["proof_node"]
                    proof_node["node_id"] = parent_id # Перезаписываем ID для строгой связности
                    nodes[parent_id] = proof_node

            except json.JSONDecodeError:
                print(f"Предупреждение: Ошибка парсинга JSON на строке {line_num}")

    # Шаг 2: Поиск корня дерева (узла, у которого нет родителя)
    all_parents = set(nodes.keys())
    roots = all_parents - all_children

    if not roots:
        print("Ошибка: Корень дерева не найден (возможно циклическая зависимость или пустой файл).")
        return
    elif len(roots) > 1:
        print(f"Предупреждение: Найдено несколько корней {roots}. Дерево будет собрано от {list(roots)[0]}")

    root_id = list(roots)[0]
    print(f"Найден корень дерева: ID {root_id}")

    # Шаг 3: Рекурсивная склейка дерева
    sys.setrecursionlimit(20000) # Увеличиваем лимит рекурсии на случай глубокого дерева
    
    def build_tree(current_id):
        if current_id not in nodes:
            print(f"Предупреждение: Нет данных для дочернего узла {current_id}. Вставляю заглушку.")
            return {"node_id": current_id, "type": "leaf", "formula": [], "tau": 100.0, "vector": [0], "children": []}

        node = nodes[current_id]

        # Если это макро-узел, собираем его детей
        if "children_ids" in node:
            children = []
            for child_id in node["children_ids"]:
                children.append(build_tree(child_id))
            node["children"] = children
            del node["children_ids"] # Убираем временный ключ, Lean 4 его не ждет

        return node

    print("Склеиваю дерево воедино...")
    full_tree = build_tree(root_id)

    # Шаг 4: Вычисление максимальной глубины
    def calculate_depth(node):
        if not node.get("children"):
            return 1
        return 1 + max(calculate_depth(c) for c in node["children"])

    max_depth = calculate_depth(full_tree)
    print("--------------------------------------------------")
    print(f"Сборка завершена успешно!")
    print(f"Всего обработано уникальных узлов: {len(nodes)}")
    print(f"Максимальная глубина (высота) сертификата: {max_depth}")
    print("--------------------------------------------------")

    # Шаг 5: Сохранение результата
    # Используем compact-запись без переносов строк (separators=(',', ':')), 
    # чтобы не раздувать файл пробелами — Lean 4 парсит это моментально.
    output_data = {"proof_tree": [full_tree]}
    print(f"Сохраняю итоговый сертификат в {output_file}...")
    
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(output_data, f, separators=(',', ':'))

    print("Готово!")

if __name__ == "__main__":
    INPUT_LOG = "pre_certificate.jsonl"
    OUTPUT_CERT = "proof_tree.json"
    
    assemble_certificate(INPUT_LOG, OUTPUT_CERT)