"""Exhaustive finite cross-system trace checker and shortest separating words.

Deterministic complete machines share one ordered operator alphabet. Positive
results carry a reachable cross-bisimulation; negative results carry a shortest
word with state/output trace. No claim about unbounded or probabilistic systems.
"""
from collections import deque
from dataclasses import dataclass
import argparse
import json
from pathlib import Path


@dataclass(frozen=True)
class Machine:
    outputs: tuple
    steps: tuple  # each action is a total function of state index


def validate(a, b, actions, start):
    if not actions or len(set(actions)) != len(actions) or not all(
            isinstance(op, str) and op for op in actions):
        raise ValueError("operators must be distinct nonempty strings")
    for name, machine in (("left", a), ("right", b)):
        n = len(machine.outputs)
        if not n or len(machine.steps) != len(actions):
            raise ValueError(name + " has missing states or operations")
        for op, row in zip(actions, machine.steps):
            if len(row) != n or any(type(j) is not int or not 0 <= j < n for j in row):
                raise ValueError(name + "." + op + " is not total")
    if len(start) != 2 or any(type(x) is not int for x in start) or not (
            0 <= start[0] < len(a.outputs) and 0 <= start[1] < len(b.outputs)):
        raise ValueError("initial state pair outside machines")


def shortest_word(a, b, actions, start):
    """Shortest output mismatch, or a complete finite cross-bisimulation.

    BFS visits at most |A|*|B| state pairs and a shortest separating word has
    length <= |A|*|B|-1 because it cannot repeat a paired state.
    """
    validate(a, b, actions, start)
    parents = {start: None}
    q = deque([start])
    while q:
        pair = q.popleft()
        x, y = pair
        if a.outputs[x] != b.outputs[y]:
            path = [pair]
            indices = []
            while parents[pair] is not None:
                old, op = parents[pair]
                path.append(old)
                indices.append(op)
                pair = old
            path.reverse()
            indices.reverse()
            word = [actions[i] for i in indices]
            return {
                "status": "counterexample",
                "word": word,
                "length": len(word),
                "trace": [
                    {"prefix": word[:depth], "left_state": l, "right_state": r,
                     "left_output": a.outputs[l], "right_output": b.outputs[r]}
                    for depth, (l, r) in enumerate(path)
                ],
                "examined_pairs": len(parents),
                "max_shortest_length": len(a.outputs) * len(b.outputs) - 1
            }
        for i in range(len(actions)):
            target = (a.steps[i][x], b.steps[i][y])
            if target not in parents:
                parents[target] = (pair, i)
                q.append(target)
    return {
        "status": "equivalent",
        "word": None,
        "reachable_pairs": [list(p) for p in sorted(parents)],
        "examined_pairs": len(parents),
        "max_shortest_length": len(a.outputs) * len(b.outputs) - 1
    }


def verify_certificate(a, b, actions, start, record):
    """Independently verify minimality of a witness or closure of a relation."""
    validate(a, b, actions, start)
    if record.get("status") == "counterexample":
        word = record.get("word")
        if not isinstance(word, list) or any(op not in actions for op in word):
            return False
        pair = start
        front = {start}
        trace = []
        for depth in range(len(word) + 1):
            x, y = pair
            trace.append({"prefix": word[:depth], "left_state": x, "right_state": y,
                          "left_output": a.outputs[x], "right_output": b.outputs[y]})
            if depth < len(word):
                if any(a.outputs[u] != b.outputs[v] for u, v in front):
                    return False
                action = actions.index(word[depth])
                pair = a.steps[action][x], b.steps[action][y]
                front = {(a.steps[i][u], b.steps[i][v])
                         for u, v in front for i in range(len(actions))}
        x, y = pair
        return (a.outputs[x] != b.outputs[y] and record.get("trace") == trace
                and record.get("length") == len(word)
                and len(word) <= len(a.outputs) * len(b.outputs) - 1)
    if record.get("status") == "equivalent":
        raw = record.get("reachable_pairs")
        if not isinstance(raw, list) or any(
                not isinstance(p, list) or len(p) != 2 for p in raw):
            return False
        try:
            relation = {tuple(p) for p in raw}
        except TypeError:
            return False
        if len(relation) != len(raw) or start not in relation:
            return False
        for x, y in relation:
            if (type(x) is not int or type(y) is not int
                    or not 0 <= x < len(a.outputs) or not 0 <= y < len(b.outputs)
                    or a.outputs[x] != b.outputs[y]):
                return False
            if any((a.steps[i][x], b.steps[i][y]) not in relation
                   for i in range(len(actions))):
                return False
        reached = {start}
        queue = [start]
        for x, y in queue:
            for i in range(len(actions)):
                pair = a.steps[i][x], b.steps[i][y]
                if pair not in reached:
                    reached.add(pair)
                    queue.append(pair)
        return reached == relation and record.get("word") is None
    return False


def analyze_mapping(a, b, actions, phi):
    """Strict state commutation differs from observational trace agreement."""
    validate(a, b, actions, (0, 0))
    if len(phi) != len(a.outputs) or any(
            type(i) is not int or not 0 <= i < len(b.outputs) for i in phi):
        raise ValueError("state map is not total")
    current = next((x for x in range(len(phi)) if a.outputs[x] != b.outputs[phi[x]]), None)
    square = next((
        {"state": x, "action": actions[i], "mapped_left": phi[a.steps[i][x]],
         "right_after_action": b.steps[i][phi[x]]}
        for x in range(len(phi)) for i in range(len(actions))
        if phi[a.steps[i][x]] != b.steps[i][phi[x]]), None)
    mismatches = [(x, result) for x in range(len(phi))
                  if (result := shortest_word(a, b, actions, (x, phi[x])))["status"]
                     == "counterexample"]
    first = min(mismatches, key=lambda item: (item[1]["length"], item[0])) if mismatches else None
    return {
        "strict_state_bridge": current is None and square is None,
        "observationally_sound_for_every_source_state": not mismatches,
        "first_current_output_mismatch_state": current,
        "first_raw_commutation_failure": square,
        "shortest_failure_over_all_sources": (
            {"source_state": first[0], **first[1]} if first else None)
    }


def read_machine(data, actions):
    return Machine(tuple(data["outputs"]),
                   tuple(tuple(data["transitions"][op]) for op in actions))


def demo(name):
    x = {"actions": ["toggle_hidden", "reveal_hidden"],
         "left": {"outputs": [0, 0, 1, 1],
                  "transitions": {"toggle_hidden": [1, 0, 3, 2],
                                  "reveal_hidden": [0, 2, 1, 3]}},
         "right": {"outputs": [0, 1],
                   "transitions": {"toggle_hidden": [0, 1],
                                   "reveal_hidden": [0, 1]}},
         "initial": [0, 0], "mapping": [0, 0, 1, 1]}
    if name == "delayed_failure":
        return x
    if name == "valid_forgetting":
        x["actions"] = ["flip_visible"]
        x["left"]["transitions"] = {"flip_visible": [2, 3, 0, 1]}
        x["right"]["transitions"] = {"flip_visible": [1, 0]}
        return x
    raise ValueError("unsupported demo")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--case", type=Path)
    group.add_argument("--demo", choices=["delayed_failure", "valid_forgetting"])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.case.read_text("utf-8")) if args.case else demo(args.demo)
    actions = tuple(data["actions"])
    a, b = read_machine(data["left"], actions), read_machine(data["right"], actions)
    start = tuple(data.get("initial", [0, 0]))
    record = shortest_word(a, b, actions, start)
    assert verify_certificate(a, b, actions, start, record)
    payload = {
        "algorithm": "finite-synchronous-product-BFS",
        "actions": actions, "start": start,
        "result": record, "certificate_verified": True,
        "mapping_analysis": analyze_mapping(a, b, actions, tuple(data["mapping"]))
            if "mapping" in data else None,
        "scope": "finite total deterministic systems; selected operations/observations"
    }
    output = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
