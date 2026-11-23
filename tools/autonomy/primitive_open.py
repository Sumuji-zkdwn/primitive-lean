#!/usr/bin/env python3
"""Primitive Open Search: proof-gated adaptive experiment synthesis.

Unlike primitive_v2's fixed list of 123 candidates, this enumerates possible
*edits of previously Lean-verified finite models* at each run. The search tree,
parameters, and active parents are derived from verified receipts. Individual
runs are finite and all operators come from a reviewed typed language.

No arbitrary code, LLM, new axioms, self-modified workflows, or auto-merges.
Finite state limits remain those of the existing Proof Forge.
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
from tools.autonomy import primitive_v2 as v2
from tools.autonomy import proof_forge as pf

SCHEMA = 1
STATUS = "LEAN_VERIFIED_FINITE_MUTATION_ONLY"
ZERO = "0" * 64
MAX_RECEIPTS = 256
MAX_EVALUATIONS = 1800
MAX_PARENTS = 10
HEX64 = re.compile(r"[a-f0-9]{64}\Z")
STATE_KEYS = {"schema_version", "last_utc_day", "receipts"}
RECEIPT_KEYS = {
    "id", "day", "head_sha", "upstream_head", "parent", "rule", "parameters",
    "root_model", "model", "root_kind", "root_word",
    "outcome", "word", "score", "objective", "status",
    "root_request_sha256", "request_sha256",
    "root_lean_sha256", "lean_sha256",
    "previous_sha256", "chain_sha256",
}
RULES = (
    "redirect_edge", "change_readout", "add_single_probe",
    "compose_actions", "choose_pair", "append_state"
)


def check(ok, reason):
    if not ok:
        raise ValueError(reason)


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def digest(value):
    return sha256(canonical(value)).hexdigest()


def load(path):
    return v2.read(Path(path))


def save(path, value):
    v2.save(Path(path), value)


def empty_state():
    return {"schema_version": SCHEMA, "last_utc_day": None, "receipts": []}


def day_check(day):
    v2.validate_day(day)
    return day


def upstream_head(upstream):
    check(type(upstream) is dict and type(upstream.get("cycles")) is list
          and len(upstream["cycles"]) > 0, "no verified primitive-v2 seed yet")
    return upstream["cycles"][-1]["chain_sha256"]


def upstream_at(upstream, head):
    check(type(head) is str and HEX64.fullmatch(head),
          "invalid V2 source chain anchor")
    matches = [i for i, row in enumerate(upstream["cycles"])
               if row["chain_sha256"] == head]
    check(len(matches) == 1, "V2 source receipt no longer accessible")
    prefix = upstream["cycles"][:matches[0] + 1]
    return {"schema_version": 1,
            "legacy_sha256": upstream["legacy_sha256"],
            "last_utc_day": prefix[-1]["day"], "cycles": prefix}


def parent_models(upstream, receipts):
    """Only Lean-verified V2 receipts and V3 descendants are parent sources."""
    roots = []
    for entry in upstream["cycles"][-4:]:
        _, model, _, _ = v2.model_pair(entry["spec"])
        roots.append(("v2:" + entry["chain_sha256"], fd.rename_model(model)))
    for rec in receipts[-6:]:
        roots.append(("v3:" + rec["id"], rec["model"]))
    unique, result = set(), []
    for parent, model in reversed(roots):
        name = fd.rename_model(model)
        fd.validate_model(name)
        fp = fd.model_fingerprint(name)
        if fp not in unique:
            unique.add(fp)
            result.append((parent, name))
    return result[:MAX_PARENTS]


def proposals(model):
    """Parameterized, deterministic, lazy grammar; no pre-listed examples."""
    model = fd.validate_model(model)
    n = len(model["observations"])
    m = len(model["transitions"])
    for a in range(m):
        for state in range(n):
            for dest in range(n):
                if model["transitions"][a][state] != dest:
                    yield "redirect_edge", {"action": a, "state": state, "dest": dest}
    for state in range(n):
        # Change to any already visible label, or introduce one new label.
        for label in range(min(max(model["observations"]) + 2,
                               pf.MAX_OBSERVATIONS)):
            if label != model["observations"][state]:
                yield "change_readout", {"state": state, "label": label}
    if m < pf.MAX_ACTIONS:
        for state in range(n):
            for dest in range(n):
                if state != dest:
                    yield "add_single_probe", {"state": state, "dest": dest}
        for left in range(m):
            for right in range(m):
                yield "compose_actions", {"left": left, "right": right}
    for left in range(n):
        for right in range(left + 1, n):
            if model["pair"] != [left, right]:
                yield "choose_pair", {"left": left, "right": right}
    if n < pf.MAX_STATES:
        for label in range(min(max(model["observations"]) + 2,
                               pf.MAX_OBSERVATIONS)):
            yield "append_state", {"label": label}


def balanced_proposals(model):
    """Interleave mutation families so edge rewiring cannot starve the rest."""
    by_rule = {rule: [] for rule in RULES}
    for rule, args in proposals(model):
        by_rule[rule].append((rule, args))
    for index in range(max((len(group) for group in by_rule.values()), default=0)):
        for rule in RULES:
            if index < len(by_rule[rule]):
                yield by_rule[rule][index]


def evolve(model, rule, args):
    """Interpret typed integer *data*, never code supplied by an experiment."""
    fd.validate_model(model)
    check(type(rule) is str and rule in RULES
          and type(args) is dict, "unreviewed transformation")
    n, m = len(model["observations"]), len(model["transitions"])
    out = {"schema_version": 1, "name": model["name"],
           "observations": model["observations"][:],
           "transitions": [row[:] for row in model["transitions"]],
           "pair": model["pair"][:]}
    signature = {
        "redirect_edge": ("action", "state", "dest"),
        "change_readout": ("state", "label"),
        "add_single_probe": ("state", "dest"),
        "compose_actions": ("left", "right"),
        "choose_pair": ("left", "right"),
        "append_state": ("label",),
    }
    check(set(args) == set(signature[rule]) and
          all(type(args[k]) is int for k in args), "invalid mutation parameters")
    a = args
    if rule == "redirect_edge":
        check(0 <= a["action"] < m and 0 <= a["state"] < n
              and 0 <= a["dest"] < n, "redirect outside finite machine")
        out["transitions"][a["action"]][a["state"]] = a["dest"]
    elif rule == "change_readout":
        check(0 <= a["state"] < n and
              0 <= a["label"] <= max(model["observations"]) + 1 and
              a["label"] < pf.MAX_OBSERVATIONS, "invalid observation label")
        out["observations"][a["state"]] = a["label"]
        out["observations"] = fd.normalize_labels(out["observations"])
    elif rule == "add_single_probe":
        check(m < pf.MAX_ACTIONS and 0 <= a["state"] < n
              and 0 <= a["dest"] < n, "new probe exceeds state/action bounds")
        row = list(range(n))
        row[a["state"]] = a["dest"]
        out["transitions"].append(row)
    elif rule == "compose_actions":
        check(m < pf.MAX_ACTIONS and 0 <= a["left"] < m
              and 0 <= a["right"] < m, "composition exceeds action bound")
        lhs, rhs = model["transitions"][a["left"]], model["transitions"][a["right"]]
        out["transitions"].append([lhs[rhs[x]] for x in range(n)])
    elif rule == "choose_pair":
        check(0 <= a["left"] < a["right"] < n,
              "observer pair must consist of distinct existing states")
        out["pair"] = [a["left"], a["right"]]
    elif rule == "append_state":
        check(n < pf.MAX_STATES and
              0 <= a["label"] <= max(model["observations"]) + 1 and
              a["label"] < pf.MAX_OBSERVATIONS, "state extension over bound")
        out["observations"].append(a["label"])
        for row in out["transitions"]:
            row.append(n)  # strict absorbing state for every action
        out["pair"] = [model["pair"][0], n]
        out["observations"] = fd.normalize_labels(out["observations"])
    out = fd.rename_model(out)
    fd.validate_model(out)
    check(fd.model_fingerprint(out) != fd.model_fingerprint(model),
          "identity / redundant transformation is not a new candidate")
    return out


def checked(model):
    result = pf.solve(model)
    pf.validate_result(model, result)
    return result


def evaluate(parent, target, history, rule):
    a, b = checked(parent), checked(target)
    olds = Counter(row["rule"] for row in history)
    outcomes = Counter(row["outcome"] for row in history)
    depths = Counter((len(row["word"]) if row["word"] is not None else -1)
                     for row in history)
    sizes = Counter(len(row["model"]["observations"]) for row in history)
    flipped = a["kind"] != b["kind"]
    old_depth = len(a["word"]) if a["kind"] == "DISTINGUISHABLE" else -1
    new_depth = len(b["word"]) if b["kind"] == "DISTINGUISHABLE" else -1
    if flipped:
        objective, structural = "DISTINGUISHABILITY_CHANGED", 14
    elif old_depth != new_depth:
        objective, structural = "SHORTEST_WORD_LENGTH_CHANGED", 10
    elif len(parent["observations"]) != len(target["observations"]):
        objective, structural = "STATE_SPACE_EXPANDED", 6
    elif len(parent["transitions"]) != len(target["transitions"]):
        objective, structural = "ACTION_VOCABULARY_CHANGED", 5
    else:
        objective, structural = "FINITE_SEMANTICS_RETAINED", 1
    score = (structural
             + (8 if olds[rule] == 0 else 0)
             + (5 if outcomes[b["kind"]] == 0 else 0)
             + (5 if depths[new_depth] == 0 else 0)
             + (3 if sizes[len(target["observations"])] == 0 else 0)
             + (2 if len(target["transitions"]) > len(parent["transitions"]) else 0))
    if new_depth == 0:
        score -= 4  # A changed observation is not automatically deep research.
    return score, objective, a, b


def select(upstream, history):
    """Search new edges of the verified graph, not a hard-coded candidate list."""
    parents = parent_models(upstream, history)
    checked_parents = {fd.model_fingerprint(m) for _, m in parents}
    seen = checked_parents | {fd.model_fingerprint(r["model"]) for r in history}
    offerings = []
    iters = [(name, model, iter(balanced_proposals(model))) for name, model in parents]
    evaluations = 0
    while iters and evaluations < MAX_EVALUATIONS:
        still = []
        for parent_id, root, options in iters:
            if evaluations >= MAX_EVALUATIONS:
                break
            try:
                rule, args = next(options)
            except StopIteration:
                continue
            still.append((parent_id, root, options))
            evaluations += 1
            try:
                child = evolve(root, rule, args)
            except ValueError as err:
                if str(err) != "identity / redundant transformation is not a new candidate":
                    raise
                continue
            fingerprint = fd.model_fingerprint(child)
            if fingerprint in seen:
                continue
            score, objective, _, _ = evaluate(root, child, history, rule)
            # A stable tie breaker favors multiple parent lineages.
            rank = (-score, len(child["observations"]),
                    len(child["transitions"]), parent_id, rule,
                    canonical(args).decode("utf-8"))
            offerings.append((rank, {"parent": parent_id,
                                     "rule": rule, "parameters": args,
                                     "root_model": root, "model": child,
                                     "score": score, "objective": objective}))
        iters = still
    if not offerings:
        return None, evaluations
    offerings.sort(key=lambda item: item[0])
    return offerings[0][1], evaluations


def model_hashes(root, target):
    hashes = {}
    for prefix, model in (("root", root), ("", target)):
        result = checked(model)
        code, _ = pf.lean_source(model, result)
        hashes[prefix + ("_request_sha256" if prefix else "request_sha256")] = sha256(
            v2.request_bytes(model)).hexdigest()
        hashes[prefix + ("_lean_sha256" if prefix else "lean_sha256")] = sha256(
            code.encode("utf-8")).hexdigest()
    return hashes


def validate_state(root, upstream, state):
    v2.validate_state(root, upstream)
    check(type(state) is dict and set(state) == STATE_KEYS
          and type(state["schema_version"]) is int
          and state["schema_version"] == SCHEMA, "invalid open-search state schema")
    records = state["receipts"]
    check(type(records) is list and len(records) <= MAX_RECEIPTS,
          "invalid receipt count")
    if not records:
        check(state["last_utc_day"] is None, "empty state has last day")
        return
    previous, last_day, accepted = ZERO, None, []
    for rec in records:
        check(type(rec) is dict and set(rec) == RECEIPT_KEYS,
              "malformed research receipt")
        day_check(rec["day"])
        check(last_day is None or rec["day"] > last_day,
              "receipt days must increase")
        last_day = rec["day"]
        check(type(rec["head_sha"]) is str and pf.HEAD.fullmatch(rec["head_sha"]),
              "invalid exact source head")
        check(rec["status"] == STATUS and
              rec["previous_sha256"] == previous,
              "unverified or broken receipt ancestry")
        source = upstream_at(upstream, rec["upstream_head"])
        available = {parent_id: model for parent_id, model in
                     parent_models(source, accepted)}
        check(rec["parent"] in available and
              rec["root_model"] == available[rec["parent"]],
              "unverified parent or changed upstream semantics")
        model = evolve(rec["root_model"], rec["rule"], rec["parameters"])
        check(model == rec["model"], "child does not follow typed grammar")
        old, new = checked(rec["root_model"]), checked(model)
        check((rec["root_kind"], rec["root_word"]) ==
              (old["kind"], old.get("word")) and
              (rec["outcome"], rec["word"]) ==
              (new["kind"], new.get("word")), "observational claims drifted")
        score, objective, _, _ = evaluate(rec["root_model"], model,
                                          accepted, rec["rule"])
        check(rec["score"] == score and rec["objective"] == objective,
              "stored feedback score drifted")
        check(all(rec[field] == value for field, value in
                  model_hashes(rec["root_model"], model).items()),
              "request or Lean digest drifted")
        check(rec["id"] == "po_" + digest({
            "parent": rec["parent"], "rule": rec["rule"],
            "parameters": rec["parameters"], "child": model["name"]})[:20],
            "invalid proposal identity")
        check(type(rec["chain_sha256"]) is str and
              HEX64.fullmatch(rec["chain_sha256"]) and
              rec["chain_sha256"] == digest({k: v for k, v in rec.items()
                                            if k != "chain_sha256"}),
              "tampered SHA-256 chain")
        previous = rec["chain_sha256"]
        accepted.append(rec)
    check(state["last_utc_day"] == last_day,
          "final day does not match receipt ledger")


def plan(root, upstream, state, day, head):
    day_check(day)
    check(type(head) is str and pf.HEAD.fullmatch(head),
          "exact 40-char commit SHA required")
    validate_state(root, upstream, state)
    check(state["last_utc_day"] is None or state["last_utc_day"] <= day,
          "UTC time moved backwards")
    if state["last_utc_day"] == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "ALREADY_VERIFIED_TODAY", "day": day, "head_sha": head}
    if len(state["receipts"]) >= MAX_RECEIPTS:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "RESOURCE_CEILING_REQUIRES_REVIEW",
                "day": day, "head_sha": head}
    selection, count = select(upstream, state["receipts"])
    if selection is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "BOUNDED_FRONTIER_NO_NEW_MODEL",
                "day": day, "head_sha": head, "searched": count}
    selected = dict(selection)
    old, new = checked(selected["root_model"]), checked(selected["model"])
    return {"schema_version": SCHEMA, "candidate": True,
            "day": day, "head_sha": head,
            "upstream_head": upstream_head(upstream),
            "proposal": {
                **selected,
                "id": "po_" + digest({
                    "parent": selected["parent"], "rule": selected["rule"],
                    "parameters": selected["parameters"],
                    "child": selected["model"]["name"]})[:20],
                "root_kind": old["kind"], "root_word": old.get("word"),
                "outcome": new["kind"], "word": new.get("word"),
                "searched": count,
            },
            "scope": "GENERATED_FINITE_OPERATOR_OBSERVABILITY_ONLY",
            "verification": "PENDING_LEAN_KERNEL"}


def prepare(root, upstream_path, state_path, day, head, output):
    upstream, state = load(upstream_path), load(state_path)
    check(not output.exists() or not any(output.iterdir()),
          "output directory must be empty; stale proofs forbidden")
    candidate = plan(root, upstream, state, day, head)
    output.mkdir(parents=True, exist_ok=True)
    if candidate["candidate"]:
        proposal = candidate["proposal"]
        requests = output / "requests"
        requests.mkdir()
        for model in (proposal["root_model"], proposal["model"]):
            path = requests / (model["name"] + ".json")
            path.write_bytes(v2.request_bytes(model))
            check(pf.read_request(path) == model,
                  "generated finite model violates Proof Forge schema")
        pf.generate(requests, output / "proof", head)
    save(output / "plan.json", candidate)
    print(json.dumps({"candidate": candidate["candidate"],
                      "id": candidate.get("proposal", {}).get("id"),
                      "reason": candidate.get("reason"), "scope": "FINITE_ONLY"}))
    return candidate


def verify_evidence(evidence, selected):
    manifest = load(evidence / "proof/manifest.json")
    props = selected["proposal"]
    a, b = props["root_model"], props["model"]
    names = [a["name"], b["name"]]
    check(len(set(names)) == 2 and
          set(manifest.get("models", [])) == set(names) and
          len(manifest.get("models", [])) == 2 and
          manifest.get("checkout_sha") == selected["head_sha"] and
          manifest.get("passed") is True, "two independent audited proofs required")
    result = {}
    for role, model in (("root", a), ("target", b)):
        path = evidence / "requests" / (model["name"] + ".json")
        check(path.is_file() and not path.is_symlink()
              and path.read_bytes() == v2.request_bytes(model),
              "request bytes differ from trusted grammar")
        src = evidence / "proof" / (model["name"] + ".lean")
        code, theorems = pf.lean_source(model, checked(model))
        check(src.is_file() and not src.is_symlink()
              and src.read_bytes() == code.encode("utf-8"),
              "Lean source differs from trusted grammar")
        metadata = load(evidence / "proof" / (model["name"] + ".json"))
        check(metadata.get("status") == "LEAN_VERIFIED" and
              metadata.get("kernel_verified") is True and
              metadata.get("checkout_sha") == selected["head_sha"] and
              metadata.get("theorems") == theorems and
              metadata.get("axiom_audit", {}).get("passed") is True and
              metadata.get("python_result") == checked(model) and
              metadata.get("request_sha256") ==
              sha256(path.read_bytes()).hexdigest() and
              metadata.get("generated_lean_sha256") ==
              sha256(src.read_bytes()).hexdigest(), "unverified certificate metadata")
        exitpath = evidence / "proof" / (model["name"] + ".exit")
        check(exitpath.is_file() and exitpath.read_text("utf-8").strip() == "0",
              "Lean did not compile successfully")
        prefix = "root_" if role == "root" else ""
        result[prefix + "request_sha256"] = metadata["request_sha256"]
        result[prefix + "lean_sha256"] = metadata["generated_lean_sha256"]
    return result


def receipt(root, upstream_path, state_path, head, evidence, output):
    upstream, state = load(upstream_path), load(state_path)
    submitted = load(evidence / "plan.json")
    expected = plan(root, upstream, state, submitted["day"], head)
    check(submitted == expected and expected["candidate"],
          "altered plan or stale upstream/state: no commit")
    check(pf.audit(evidence / "proof") == 0,
          "proof or axiom audit failed")
    hashes = verify_evidence(evidence, expected)
    proposal = expected["proposal"]
    row = {key: proposal[key] for key in (
        "id", "parent", "rule", "parameters", "root_model", "model",
        "root_kind", "root_word", "outcome", "word", "score", "objective")}
    row.update({"day": expected["day"], "head_sha": head,
                "upstream_head": expected["upstream_head"],
                "status": STATUS, "previous_sha256":
                    state["receipts"][-1]["chain_sha256"]
                    if state["receipts"] else ZERO,
                **hashes})
    row["chain_sha256"] = digest(row)
    candidate = {"schema_version": SCHEMA, "last_utc_day": expected["day"],
                 "receipts": state["receipts"] + [row]}
    validate_state(root, upstream, candidate)
    check(not output.is_symlink(), "state output symlink forbidden")
    save(output, candidate)
    print(json.dumps({"verified": row["id"], "parent": row["parent"],
                      "rule": row["rule"], "score": row["score"],
                      "outcome": row["outcome"], "receipts": len(candidate["receipts"])}))
    return candidate


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("prepare", "receipt"))
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--day", required=False)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--evidence", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "prepare":
            check(args.day is not None, "--day required")
            prepare(args.root, args.upstream, args.state, args.day,
                    args.head, args.output)
        else:
            check(args.evidence is not None, "--evidence required")
            receipt(args.root, args.upstream, args.state, args.head,
                    args.evidence, args.output)
    except (ValueError, OSError, TypeError, KeyError, IndexError) as exc:
        print("PRIMITIVE_OPEN_SEARCH_ERROR: " + str(exc), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
