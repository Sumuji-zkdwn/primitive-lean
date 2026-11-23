#!/usr/bin/env python3
"""Proof-gated search for new finite observational *definitions* and criteria.

The objects generated are typed JSON expressions, not arbitrary programs.
A separate Lean theorem checks the candidate expression against the complete
generated observation table, while Proof Forge certifies the pairwise
observational question. A bounded Python search evaluates alternative
criterion definitions; that heuristic is NOT a Lean theorem.

Source histories are independently verified data. Only an isolated, JSON-only
result branch is writable by the separate successful Actions publisher.
"""
from __future__ import annotations

from collections import Counter
from datetime import date
from hashlib import sha256
import argparse
import json
from pathlib import Path
import re
import sys

from tools.autonomy import finite_discovery as fd
from tools.autonomy import proof_forge as pf
from tools.autonomy import strategy_evolution as strategies

SCHEMA = 1
LIMIT = 40
MAX_NODES = 9
MAX_DEPTH = 4
MAX_ROOTS = 12
MAX_PROPOSALS = 600
STATUS = "LEAN_VERIFIED_FINITE_DEFINITION_ONLY"
HASH = re.compile(r"[a-f0-9]{64}\Z")
NAME = re.compile(r"define_[a-f0-9]{16}\Z")
CRITERIA = (
    ("pair_flip", "either"),
    ("global_distinctions", "increase"),
    ("global_distinctions", "decrease"),
    ("minimum_depth", "decrease"),
    ("minimum_depth", "increase"),
    ("readout_colors", "increase"),
    ("readout_colors", "decrease"),
)
RECEIPT_KEYS = {
    "id", "date", "head_sha", "catalog_sha256", "finite_state_sha256",
    "strategy_state_sha256", "source_id", "source_sha256", "parent",
    "expression", "criterion", "base_model", "derived_model",
    "baseline", "derived", "score", "metric",
    "base_request_sha256", "derived_request_sha256",
    "base_lean_sha256", "derived_lean_sha256", "semantics_sha256",
    "status", "previous_sha256", "chain_sha256",
}
STATE_KEYS = {"schema_version", "catalog_sha256", "last_utc_day", "receipts"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


def digest(obj):
    return sha256(canonical(obj)).hexdigest()


def load(path):
    require(path.is_file() and not path.is_symlink(), "missing or symlinked JSON evidence")
    require(path.stat().st_size <= 600_000, "JSON evidence exceeds size bound")
    return json.loads(path.read_text(encoding="utf-8"),
                      object_pairs_hook=pf.object_no_duplicates)


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True,
                               ensure_ascii=False) + "\n", encoding="utf-8")


def check_day(value):
    require(type(value) is str and bool(re.fullmatch(r"\d{4}-\d{2}-\d{2}", value)),
            "UTC date must be YYYY-MM-DD")
    require(date.fromisoformat(value).isoformat() == value, "invalid UTC calendar day")
    return value


def empty_state():
    return {"schema_version": SCHEMA, "catalog_sha256": None,
            "last_utc_day": None, "receipts": []}


def expr_shape(node, actions, depth=1):
    """Check syntax, types and bounded expression complexity. No evaluation."""
    require(type(node) is dict and depth <= MAX_DEPTH, "invalid expression node/depth")
    op = node.get("op")
    if op == "read":
        require(set(node) == {"op"}, "read expression has extra fields")
        return "color", 1
    if op == "after":
        require(set(node) == {"op", "action", "arg"}, "invalid after expression")
        a = node["action"]
        require(type(a) is int and 0 <= a < actions, "after action out of bounds")
        typ, size = expr_shape(node["arg"], actions, depth+1)
        require(size+1 <= MAX_NODES, "expression too large")
        return typ, size+1
    if op == "bit":
        require(set(node) == {"op", "arg", "label"}, "invalid bit expression")
        label = node["label"]
        require(type(label) is int and 0 <= label < pf.MAX_OBSERVATIONS,
                "non-finite observation label")
        typ, size = expr_shape(node["arg"], actions, depth+1)
        require(typ == "color" and size+1 <= MAX_NODES, "bit expects a color")
        return "flag", size+1
    if op in ("eq", "xor", "pair"):
        require(set(node) == {"op", "left", "right"}, "invalid binary expression")
        lt, ls = expr_shape(node["left"], actions, depth+1)
        rt, rs = expr_shape(node["right"], actions, depth+1)
        if op == "eq":
            require(lt == rt, "equality arguments must have the same type")
            result = "flag"
        else:
            require(lt == "flag" and rt == "flag",
                    "xor and pair require two Boolean flags")
            result = "color" if op == "pair" else "flag"
        require(ls + rs + 1 <= MAX_NODES, "expression exceeds node budget")
        return result, ls + rs + 1
    raise ValueError("unapproved observation-definition operator")


def eval_expression(node, machine, state):
    """Executable *interpreter* for validated data, never source evaluation."""
    op = node["op"]
    if op == "read":
        return machine["observations"][state]
    if op == "after":
        return eval_expression(node["arg"], machine,
                               machine["transitions"][node["action"]][state])
    if op == "bit":
        return int(eval_expression(node["arg"], machine, state) == node["label"])
    a = eval_expression(node["left"], machine, state)
    b = eval_expression(node["right"], machine, state)
    if op == "eq":
        return int(a == b)
    if op == "xor":
        return (a + b) % 2
    if op == "pair":
        return a + 2*b
    raise ValueError("unknown approved expression")


def derived_model(machine, expression):
    fd.validate_model(machine)
    expr_shape(expression, len(machine["transitions"]))
    values = [eval_expression(expression, machine, s)
              for s in range(len(machine["observations"]))]
    require(all(type(x) is int and 0 <= x < pf.MAX_OBSERVATIONS for x in values),
            "expression is not bounded finite observation")
    target = dict(machine)
    target["observations"] = values
    target = fd.rename_model(target)
    fd.validate_model(target)
    return target


def expression_candidates(machine):
    """Small typed grammar; generates NEW definitions as serializable data."""
    n_actions = len(machine["transitions"])
    read = {"op": "read"}
    candidates = []
    for a in range(min(2, n_actions)):
        once = {"op": "after", "action": a, "arg": read}
        twice = {"op": "after", "action": a, "arg": once}
        candidates.extend([once, twice,
                           {"op": "eq", "left": read, "right": once}])
        for label in sorted(set(machine["observations"]))[:2]:
            b0 = {"op": "bit", "label": label, "arg": read}
            b1 = {"op": "bit", "label": label, "arg": once}
            candidates.extend([
                b0, b1,
                {"op": "xor", "left": b0, "right": b1},
                {"op": "pair", "left": b0, "right": b1},
            ])
    candidates.append({"op": "eq", "left": read, "right": read})
    unique = {}
    for expression in candidates:
        try:
            expr_shape(expression, n_actions)
            target = derived_model(machine, expression)
        except ValueError:
            continue
        if fd.model_fingerprint(machine) == fd.model_fingerprint(target):
            continue
        unique.setdefault(digest(expression), expression)
    return list(unique.values())


def checked(model):
    fd.validate_model(model)
    result = pf.solve(model)
    pf.validate_result(model, result)
    return result


def global_pairs(machine):
    """Partition-refinement count, cross-checkable by independent all-pairs BFS."""
    labels = fd.observational_partition(machine)
    return sum(labels[i] != labels[j]
               for i in range(len(labels)) for j in range(i+1, len(labels)))


def verify_global_pairs(machine):
    """Independent product-automaton check of every unordered pair."""
    n = len(machine["observations"])
    counted = 0
    for x in range(n):
        for y in range(x+1, n):
            instance = dict(machine, pair=[x, y])
            answer = checked(instance)
            counted += answer["kind"] == "DISTINGUISHABLE"
    require(counted == global_pairs(machine),
            "independent finite-observer methods disagree")
    return counted


def objective_result(base, derived, criterion):
    require(type(criterion) is dict and set(criterion) == {"metric", "direction"}
            and (criterion["metric"], criterion["direction"]) in CRITERIA,
            "unknown mathematical evaluation criterion")
    a, b = checked(base), checked(derived)
    metric, direction = criterion["metric"], criterion["direction"]
    if metric == "pair_flip":
        value = int(a["kind"] != b["kind"])
        score = 12 * value
    elif metric == "global_distinctions":
        old, new = global_pairs(base), global_pairs(derived)
        value = new-old
        signed = value if direction == "increase" else -value
        score = min(12, 3*max(0, signed))
    elif metric == "minimum_depth":
        if a["kind"] != "DISTINGUISHABLE" or b["kind"] != "DISTINGUISHABLE":
            value, score = 0, 0
        else:
            value = len(b["word"])-len(a["word"])
            signed = -value if direction == "decrease" else value
            score = min(12, 4*max(0, signed))
    else:
        value = len(set(derived["observations"])) - len(set(base["observations"]))
        signed = value if direction == "increase" else -value
        score = min(12, 3*max(0, signed))
    return {"baseline_kind": a["kind"], "derived_kind": b["kind"],
            "baseline_word": a.get("word"), "derived_word": b.get("word"),
            "value": int(value), "score": int(score),
            "metric": metric, "direction": direction}


def get_catalog(root):
    catalog, sources = fd.seeds(root)
    return catalog, sources


def active_roots(root, fd_upstream, strategy_upstream, state):
    """Review source bytes; use prior certified research as *data*."""
    fd.validate_state(root, fd_upstream)
    strategies.validate_state(root, strategy_upstream)
    catalog, seeds = get_catalog(root)
    roots = [
        {"source_id": "reviewed:" + row["seed"],
         "source_sha256": digest(row), "parent": None,
         "model": row["model"]}
        for row in seeds
    ]
    for item in fd_upstream["receipts"][-4:]:
        roots.append({"source_id": "finite:" + item["name"],
                      "source_sha256": item["chain_sha256"],
                      "parent": None, "model": item["model"]})
    for item in strategy_upstream["receipts"][-2:]:
        roots.append({"source_id": "strategy:" + item["id"],
                      "source_sha256": item["chain_sha256"],
                      "parent": None, "model": item["model"]})
    for item in state["receipts"][-4:]:
        roots.append({"source_id": "foundry:" + item["id"],
                      "source_sha256": item["chain_sha256"],
                      "parent": item["id"], "model": item["derived_model"]})
    require(len(roots) <= MAX_ROOTS+4, "too many reviewed source roots")
    for item in roots:
        fd.validate_model(item["model"])
    return catalog, roots


def definition_id(source_id, base_model, expression, criterion):
    return "define_" + digest({
        "source": source_id,
        "base": fd.model_fingerprint(base_model),
        "expression": expression, "criterion": criterion,
    })[:16]


def validate_state(root, state):
    require(type(state) is dict and set(state) == STATE_KEYS,
            "invalid definition ledger schema")
    require(type(state["schema_version"]) is int and
            state["schema_version"] == SCHEMA, "unsupported definition ledger version")
    require(type(state["receipts"]) is list and len(state["receipts"]) <= LIMIT,
            "definition ledger exceeds bound")
    catalog, _ = get_catalog(root)
    if not state["receipts"]:
        require(state["catalog_sha256"] is None and
                state["last_utc_day"] is None, "empty ledger has history")
        return state
    require(state["catalog_sha256"] == catalog, "reviewed catalog mismatch")
    used = {}
    prev, last_day = "0"*64, None
    for item in state["receipts"]:
        require(type(item) is dict and set(item) == RECEIPT_KEYS,
                "malformed verified definition receipt")
        name = item["id"]
        require(type(name) is str and NAME.fullmatch(name) and name not in used,
                "invalid or duplicate definition identifier")
        base = fd.validate_model(item["base_model"])
        target = fd.validate_model(item["derived_model"])
        expected = derived_model(base, item["expression"])
        require(target == expected, "definition does not generate recorded observation")
        require(item["id"] == definition_id(item["source_id"], base,
                                             item["expression"], item["criterion"]),
                "definition identifier mismatch")
        parent = item["parent"]
        if parent is not None:
            require(parent in used and
                    item["base_model"] == used[parent]["derived_model"] and
                    item["source_id"] == "foundry:"+parent and
                    item["source_sha256"] == used[parent]["chain_sha256"],
                    "definition parent not a prior verified result")
        else:
            require(type(item["source_id"]) is str and
                    item["source_id"].startswith(("reviewed:", "finite:", "strategy:")),
                    "root definition has untrusted provenance")
        check_day(item["date"])
        require(last_day is None or item["date"] > last_day,
                "definition history days not increasing")
        last_day = item["date"]
        for key in ("source_sha256", "catalog_sha256", "finite_state_sha256",
                    "strategy_state_sha256", "base_request_sha256",
                    "derived_request_sha256", "base_lean_sha256",
                    "derived_lean_sha256", "semantics_sha256",
                    "previous_sha256", "chain_sha256"):
            require(type(item[key]) is str and bool(HASH.fullmatch(item[key])),
                    "malformed source/proof evidence hash")
        require(item["catalog_sha256"] == catalog and
                item["previous_sha256"] == prev and
                item["status"] == STATUS, "invalid chain, catalog or proof status")
        old = checked(base)
        new = checked(target)
        require(item["baseline"] == old and item["derived"] == new,
                "unverified outcome or noncanonical finite result")
        calculated = objective_result(base, target, item["criterion"])
        require(item["metric"] == calculated and
                item["score"] == calculated["score"],
                "mathematical criterion score was changed")
        content = {key: value for key, value in item.items()
                   if key != "chain_sha256"}
        require(item["chain_sha256"] == digest(content),
                "definition receipt hash chain mismatch")
        used[name] = item
        prev = item["chain_sha256"]
    require(state["last_utc_day"] == last_day,
            "state calendar cursor differs from last receipt")
    return state


def propose(root, fd_upstream, strategy_upstream, state):
    catalog, sources = active_roots(root, fd_upstream, strategy_upstream, state)
    seen = {entry["id"] for entry in state["receipts"]}
    used_models = {(item["source_id"],
                    fd.model_fingerprint(item["derived_model"]))
                   for item in state["receipts"]}
    domains = Counter(entry["source_id"].split(":")[0] for entry in state["receipts"])
    used_objectives = Counter(entry["criterion"]["metric"] for entry in state["receipts"])
    options = []
    for source_index, source in enumerate(sources):
        model = source["model"]
        seen_locally = set()
        for expression in expression_candidates(model):
            target = derived_model(model, expression)
            fp = fd.model_fingerprint(target)
            if (source["source_id"], fp) in used_models or fp in seen_locally:
                continue
            seen_locally.add(fp)
            for metric, direction in CRITERIA:
                if len(options) >= MAX_PROPOSALS:
                    break
                objective = {"metric": metric, "direction": direction}
                score = objective_result(model, target, objective)
                if score["score"] == 0:
                    continue
                identity = definition_id(source["source_id"], model,
                                         expression, objective)
                if identity in seen:
                    continue
                _, nodes = expr_shape(expression, len(model["transitions"]))
                # A transparent bounded heuristic, not theorem novelty.
                explore = 2 if used_objectives[metric] == 0 else 0
                rank = (
                    -(score["score"] + explore), domains[source["source_id"].split(":")[0]],
                    used_objectives[metric], nodes, source_index, identity,
                )
                options.append((rank, {
                    "id": identity, "source_id": source["source_id"],
                    "source_sha256": source["source_sha256"],
                    "parent": source["parent"], "expression": expression,
                    "criterion": objective, "base_model": model,
                    "derived_model": target, "score": score["score"],
                    "metric": score,
                }))
            if len(options) >= MAX_PROPOSALS:
                break
        if len(options) >= MAX_PROPOSALS:
            break
    if not options:
        return None, catalog
    return min(options, key=lambda t: t[0])[1], catalog


def plan(root, fd_upstream, strategy_upstream, state, head, day):
    require(type(head) is str and pf.HEAD.fullmatch(head),
            "exact immutable main head required")
    check_day(day)
    validate_state(root, state)
    fd.validate_state(root, fd_upstream)
    strategies.validate_state(root, strategy_upstream)
    if state["last_utc_day"] is not None:
        require(day >= state["last_utc_day"], "UTC day older than verified history")
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "ALREADY_VERIFIED_TODAY", "head_sha": head, "day": day}
    if len(state["receipts"]) >= LIMIT:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "DEFINITION_BUDGET_EXHAUSTED", "head_sha": head, "day": day}
    candidate, catalog = propose(root, fd_upstream, strategy_upstream, state)
    if candidate is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "TYPED_DEFINITION_GRAMMAR_EXHAUSTED",
                "head_sha": head, "day": day}
    return {
        "schema_version": SCHEMA, "candidate": True, "head_sha": head,
        "day": day, "catalog_sha256": catalog,
        "finite_state_sha256": digest(fd_upstream),
        "strategy_state_sha256": digest(strategy_upstream),
        **candidate,
        "baseline": checked(candidate["base_model"]),
        "derived": checked(candidate["derived_model"]),
        "proof_status": "PENDING_KERNEL_VERIFICATION",
        "scope": "FINITE_OBSERVATION_DEFINITION_NOT_GENERAL_PHYSICAL_MEASUREMENT",
    }


def expression_lean(node):
    op = node["op"]
    if op == "read":
        return "baseRead s"
    if op == "after":
        return expression_lean(node["arg"]).replace(" s", f" (step{node['action']} s)")
    if op == "bit":
        return f"(if {expression_lean(node['arg'])} = {node['label']} then (1 : Nat) else 0)"
    left, right = expression_lean(node["left"]), expression_lean(node["right"])
    if op == "eq":
        return f"(if {left} = {right} then (1 : Nat) else 0)"
    if op == "xor":
        return f"(({left} + {right}) % 2)"
    if op == "pair":
        return f"({left} + (2 * {right}))"
    raise ValueError("unknown expression syntax")


def expression_lean_term(node, state="s"):
    """Reference renderer with explicit state substitution, no string rewrite."""
    op = node["op"]
    if op == "read":
        return f"(baseRead {state})"
    if op == "after":
        return expression_lean_term(node["arg"],
                                    f"(step{node['action']} {state})")
    if op == "bit":
        return f"(if {expression_lean_term(node['arg'], state)} = {node['label']} then (1 : Nat) else 0)"
    left = expression_lean_term(node["left"], state)
    right = expression_lean_term(node["right"], state)
    if op == "eq":
        return f"(if {left} = {right} then (1 : Nat) else 0)"
    if op == "xor":
        return f"(({left} + {right}) % 2)"
    if op == "pair":
        return f"({left} + 2 * {right})"
    raise ValueError("unapproved expression")


def semantics_source(model, expression, target):
    """Independent Lean statement checks expression meaning for *all* states."""
    fd.validate_model(model)
    require(target == derived_model(model, expression),
            "semantic table mismatches declared observation")
    n = len(model["observations"])
    lines = [
        "import Mathlib.Tactic",
        "set_option maxRecDepth 2048",
        "set_option maxHeartbeats 1000000",
        "namespace DefinitionFoundry",
        f"abbrev State := Fin {n}",
        f"def baseRead (s : State) : Nat := {pf.ite('s.val', model['observations'], 'Nat')}",
    ]
    for i, row in enumerate(model["transitions"]):
        lines.append(f"def step{i} (s : State) : State := {pf.ite('s.val', row, 'State')}")
    lines.extend([
        f"def proposedRead (s : State) : Nat := {expression_lean_term(expression)}",
        f"def expectedRead (s : State) : Nat := {pf.ite('s.val', target['observations'], 'Nat')}",
        "theorem expression_matches_entire_table :",
        "    ∀ s : State, proposedRead s = expectedRead s := by",
        "  intro s",
        "  fin_cases s <;> decide",
        "#print axioms expression_matches_entire_table",
        "end DefinitionFoundry", "",
    ])
    return "\n".join(lines)


def audit_semantics(evidence, head, model, expression, target):
    expected = semantics_source(model, expression, target)
    path = evidence / "semantics.lean"
    require(path.is_file() and not path.is_symlink()
            and path.read_bytes() == expected.encode("utf-8"),
            "Lean expression semantics source has changed")
    result = evidence / "semantics.exit"
    log_file = evidence / "semantics.log"
    require(result.is_file() and log_file.is_file() and
            result.read_text("utf-8").strip() == "0",
            "Lean semantic theorem compilation did not succeed")
    log = log_file.read_text("utf-8", errors="replace")
    require(not re.search(r"error:|warning:|sorryAx|admit|native_decide", log),
            "Lean semantic proof emitted a warning/error/unsupported axiom")
    require("does not depend on any axioms" in log or
            "depends on axioms:" in log,
            "missing Lean semantic axiom evidence")
    axioms = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
    for a in axioms:
        found = {name.strip() for name in a.split(",") if name.strip()}
        require(found <= pf.ALLOWED_AXIOMS, "unsupported semantic proof axiom")
    return sha256(expected.encode("utf-8")).hexdigest()


def prepare(root, fd_file, strategy_file, state_file, head, day, output):
    upstream, strategy, state = load(fd_file), load(strategy_file), load(state_file)
    require(not output.exists() or not any(output.iterdir()),
            "output must be empty before preparing evidence")
    selected = plan(root, upstream, strategy, state, head, day)
    output.mkdir(parents=True)
    if selected["candidate"]:
        requests = output / "requests"
        requests.mkdir()
        for model in (selected["base_model"], selected["derived_model"]):
            path = requests / (model["name"] + ".json")
            save(path, model)
            require(pf.read_request(path) == model,
                    "typed definition model failed Proof Forge schema")
        pf.generate(requests, output / "proof", head)
        (output / "semantics.lean").write_text(
            semantics_source(selected["base_model"], selected["expression"],
                             selected["derived_model"]), encoding="utf-8")
    save(output / "plan.json", selected)
    print(json.dumps({"candidate": selected["candidate"],
                      "definition": selected.get("id"),
                      "criterion": selected.get("criterion"),
                      "score": selected.get("score"),
                      "status": "UNVERIFIED_DEFINITION" if selected["candidate"]
                      else selected["reason"]}))
    return selected


def receipt(root, fd_file, strategy_file, state_file, head, evidence, output):
    upstream, strategy, state = load(fd_file), load(strategy_file), load(state_file)
    given = load(evidence / "plan.json")
    require(given.get("candidate") is True, "no new definition to certify")
    expected = plan(root, upstream, strategy, state, head, given.get("day"))
    require(given == expected, "definition plan or upstream changed after proof")
    require(pf.audit(evidence / "proof") == 0,
            "dual finite Lean proof or axiom audit failed")
    base, target = expected["base_model"], expected["derived_model"]
    semhash = audit_semantics(evidence, head, base, expected["expression"], target)
    names = sorted([base["name"], target["name"]])
    require(len(set(names)) == 2, "identical baseline and derived model")
    manifest = load(evidence / "proof/manifest.json")
    require(manifest.get("passed") is True and
            manifest.get("checkout_sha") == head and
            manifest.get("models") == names,
            "two exact-head finite certificates required")
    proven = {}
    for model in (base, target):
        name = model["name"]
        request = evidence / "requests" / (name+".json")
        require(pf.read_request(request) == model,
                "source model request altered after generation")
        result = checked(model)
        expected_lean, theorems = pf.lean_source(model, result)
        source = evidence / "proof" / (name+".lean")
        require(source.is_file() and not source.is_symlink() and
                source.read_bytes() == expected_lean.encode("utf-8"),
                "generated Lean source does not match deterministic model")
        report = load(evidence / "proof" / (name+".json"))
        require(report.get("model") == name and
                report.get("checkout_sha") == head and
                report.get("theorems") == theorems and
                report.get("status") == "LEAN_VERIFIED" and
                report.get("kernel_verified") is True and
                report.get("axiom_audit", {}).get("passed") is True and
                report.get("python_result") == result and
                report.get("generated_lean_sha256") == sha256(source.read_bytes()).hexdigest() and
                report.get("request_sha256") == sha256(request.read_bytes()).hexdigest(),
                "finite certificate fails exact reconstruction")
        proven[name] = report
    # The full-partition comparison is independently reproduced in Python.
    verify_global_pairs(base)
    verify_global_pairs(target)
    metric = objective_result(base, target, expected["criterion"])
    require(metric == expected["metric"], "criterion changed after validation")
    previous = state["receipts"][-1]["chain_sha256"] if state["receipts"] else "0"*64
    saved = {
        "id": expected["id"], "date": expected["day"], "head_sha": head,
        "catalog_sha256": expected["catalog_sha256"],
        "finite_state_sha256": expected["finite_state_sha256"],
        "strategy_state_sha256": expected["strategy_state_sha256"],
        "source_id": expected["source_id"],
        "source_sha256": expected["source_sha256"], "parent": expected["parent"],
        "expression": expected["expression"], "criterion": expected["criterion"],
        "base_model": base, "derived_model": target,
        "baseline": expected["baseline"], "derived": expected["derived"],
        "score": expected["score"], "metric": metric,
        "base_request_sha256": proven[base["name"]]["request_sha256"],
        "derived_request_sha256": proven[target["name"]]["request_sha256"],
        "base_lean_sha256": proven[base["name"]]["generated_lean_sha256"],
        "derived_lean_sha256": proven[target["name"]]["generated_lean_sha256"],
        "semantics_sha256": semhash,
        "status": STATUS, "previous_sha256": previous,
    }
    saved["chain_sha256"] = digest(saved)
    state["receipts"].append(saved)
    state["catalog_sha256"] = expected["catalog_sha256"]
    state["last_utc_day"] = expected["day"]
    validate_state(root, state)
    save(output, state)
    print(json.dumps({"accepted": saved["id"],
                      "metric": metric["metric"], "score": saved["score"],
                      "source": saved["source_id"],
                      "total_verified_definitions": len(state["receipts"])}))
    return saved


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("prepare", "receipt"):
        p = commands.add_parser(name)
        p.add_argument("--root", required=True, type=Path)
        p.add_argument("--finite", required=True, type=Path)
        p.add_argument("--strategy", required=True, type=Path)
        p.add_argument("--state", required=True, type=Path)
        p.add_argument("--head", required=True)
        p.add_argument("--output", required=True, type=Path)
        if name == "prepare":
            p.add_argument("--day", required=True)
        else:
            p.add_argument("--evidence", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "prepare":
            prepare(args.root.resolve(), args.finite, args.strategy, args.state,
                    args.head, args.day, args.output)
        else:
            receipt(args.root.resolve(), args.finite, args.strategy, args.state,
                    args.head, args.evidence, args.output)
    except (ValueError, OSError, TypeError, KeyError, UnicodeError,
            json.JSONDecodeError) as exc:
        print("DEFINITION_FOUNDRY_FAIL_CLOSED:", str(exc), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
