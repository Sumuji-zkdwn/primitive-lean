#!/usr/bin/env python3
"""Primitive Autonomy V2: bounded, proof-gated growth from the legacy operator family.

This trusted main-branch controller translates the original primitive-autonomy
finite operator witnesses into two independent Proof Forge obligations, then
uses *only verified receipts* to choose a novelty-seeking next candidate.

Legacy Lean is not re-certified here. It is used only to avoid duplicates.
No LLM, arbitrary code execution, network, new axioms, or main-branch writes.

  prepare --root DIR --state FILE --head SHA --day YYYY-MM-DD --output DIR
  receipt --root DIR --state FILE --head SHA --evidence DIR --output FILE
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

from tools.autonomy import grow
from tools.autonomy import proof_forge as pf

SCHEMA = 1
STATE_KEYS = {"schema_version", "legacy_sha256", "last_utc_day", "cycles"}
RECORD_KEYS = {
    "id", "day", "head_sha", "legacy_sha256", "spec", "novelty",
    "baseline_request_sha256", "candidate_request_sha256",
    "baseline_lean_sha256", "candidate_lean_sha256",
    "outcome", "word", "status", "previous_sha256", "chain_sha256",
}
STATUS = "LEAN_VERIFIED_FINITE_OPERATOR_COMPARISON_ONLY"
LEGACY_LEDGER = Path("docs/autonomy/ledger.json")
MAX_STATE = 12
MAX_CYCLES = 128
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
IDENT = re.compile(r"pa2_[0-9a-f]{16}\Z")
ZERO_HASH = "0" * 64


def require(value, message):
    if not value:
        raise ValueError(message)


def encode(obj):
    return json.dumps(obj, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def digest(obj):
    return sha256(encode(obj)).hexdigest()


def save(path: Path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, sort_keys=True,
                               indent=2) + "\n", encoding="utf-8")


def read(path: Path):
    require(path.is_file() and not path.is_symlink(),
            "expected a regular file: " + str(path))
    require(path.stat().st_size <= 900_000, "input exceeds size bound")
    return json.loads(path.read_text(encoding="utf-8"),
                      object_pairs_hook=pf.object_no_duplicates)


def validate_day(day):
    require(type(day) is str and re.fullmatch(r"\d{4}-\d{2}-\d{2}", day),
            "UTC date must be YYYY-MM-DD")
    require(date.fromisoformat(day).isoformat() == day, "invalid UTC date")
    return day


def empty_state():
    return {"schema_version": 1, "legacy_sha256": None,
            "last_utc_day": None, "cycles": []}


def legacy(root):
    """The original source and three audited receipts are immutable *inputs*.

    No command from that old branch is executed. Comparing original hashes
    verifies provenance; v2 does not reassert kernel validity of the old CI.
    """
    path = root / LEGACY_LEDGER
    item = read(path)
    require(type(item) is dict and set(item) == {"schema_version", "cycles"}
            and type(item["schema_version"]) is int
            and item["schema_version"] == 1, "legacy ledger schema mismatch")
    cycles = item["cycles"]
    require(type(cycles) is list and 1 <= len(cycles) <= 84,
            "legacy cycles missing or invalid")
    allowed = {
        (r["states"], r["image_of_zero"], r["image_of_one"])
        for r in grow.candidates()
    }
    seen = set()
    for index, row in enumerate(cycles, start=1):
        require(type(row) is dict and row.get("cycle") == index and
                row.get("status") == "verified", "legacy cycle unverified")
        model = row.get("model")
        require(type(model) is dict and
                set(model) == {"states", "image_of_zero", "image_of_one"},
                "legacy model schema mismatch")
        triple = (model["states"], model["image_of_zero"], model["image_of_one"])
        require(all(type(x) is int for x in triple) and
                triple in allowed and triple not in seen,
                "legacy model invalid or repeated")
        seen.add(triple)
        expected = f"linear_input/lean_check/AutonomyCycle{index:05d}.inc"
        require(row.get("source") == expected, "legacy source path mismatch")
        original = root / expected
        require(original.is_file() and not original.is_symlink(),
                "legacy Lean source missing or symlinked")
        require(sha256(original.read_bytes()).hexdigest() == row.get("sha256"),
                "legacy source bytes drifted")
    return sha256(path.read_bytes()).hexdigest(), seen


def validate_spec(spec):
    require(type(spec) is dict and type(spec.get("family")) is str,
            "invalid spec")
    family = spec["family"]
    if family == "legacy_split":
        require(set(spec) == {"family", "states", "a", "b"}, "legacy fields")
        n, a, b = spec["states"], spec["a"], spec["b"]
        require(all(type(v) is int for v in (n, a, b)) and
                3 <= n <= 8 and 0 <= a < n and 0 <= b < n and
                (a < 2) != (b < 2), "legacy witness not separating")
    elif family == "delayed_split":
        require(set(spec) == {"family", "states", "depth"}, "delayed fields")
        n, depth = spec["states"], spec["depth"]
        require(all(type(v) is int for v in (n, depth)) and
                5 <= n <= MAX_STATE and 2 <= depth <= n - 3,
                "delayed witness bounds")
    elif family == "inert_swap":
        require(set(spec) == {"family", "states"}, "inert fields")
        n = spec["states"]
        require(type(n) is int and 3 <= n <= 8, "inert witness bounds")
    else:
        raise ValueError("unreviewed research grammar: " + family)
    return spec


def catalog(legacy_seen):
    """Finite, reviewed extension: original 84 plus delayed and negative controls."""
    options = []
    for item in grow.candidates():
        triple = (item["states"], item["image_of_zero"], item["image_of_one"])
        if triple not in legacy_seen:
            options.append({"family": "legacy_split", "states": triple[0],
                            "a": triple[1], "b": triple[2]})
    for n in range(5, MAX_STATE + 1):
        for depth in range(2, n - 2):
            options.append({"family": "delayed_split", "states": n,
                            "depth": depth})
    for n in range(3, 9):
        options.append({"family": "inert_swap", "states": n})
    require(len(options) <= MAX_CYCLES, "candidate budget exceeded")
    return options


def spec_id(spec):
    return "pa2_" + digest(validate_spec(spec))[:16]


def model_pair(spec):
    """Identity-only baseline and a typed new operator for the same observer."""
    validate_spec(spec)
    n = spec["states"]
    original = list(range(n))
    next_step = original.copy()
    if spec["family"] == "delayed_split":
        observation = [0] * (n - 1) + [1]
        # 0 -> 2 -> 4 -> 5 -> ... -> (n-1); 1 -> 3 -> 3.
        # The first visible difference is at precisely 'depth' fresh steps.
        chain = [0, 2] + list(range(4, spec["depth"] + 2)) + [n - 1]
        next_step[1] = 3
        next_step[3] = 3
        for left, right in zip(chain, chain[1:]):
            next_step[left] = right
    else:
        observation = [0, 0] + [1] * (n - 2)
        if spec["family"] == "legacy_split":
            next_step[0] = spec["a"]
            next_step[1] = spec["b"]
        else:
            next_step[0], next_step[1] = 1, 0
    label = spec_id(spec)
    base = {"schema_version": 1, "name": label + "_old",
            "observations": observation, "transitions": [original],
            "pair": [0, 1]}
    new = {"schema_version": 1, "name": label + "_new",
           "observations": observation,
           "transitions": [original, next_step], "pair": [0, 1]}
    baseline, result = pf.solve(base), pf.solve(new)
    pf.validate_result(base, baseline)
    pf.validate_result(new, result)
    require(baseline["kind"] == "EQUIVALENT",
            "baseline identity is not observationally equivalent")
    if spec["family"] == "inert_swap":
        require(result["kind"] == "EQUIVALENT", "negative control failed")
    else:
        expected_length = spec["depth"] if spec["family"] == "delayed_split" else 1
        require(result["kind"] == "DISTINGUISHABLE"
                and len(result["word"]) == expected_length,
                "operator does not attain its declared shortest depth")
    return base, new, baseline, result


def novelty(spec, history):
    """Explicit coverage heuristic, *never* a mathematical truth value."""
    _, _, _, answer = model_pair(spec)
    kind = answer["kind"]
    depth = len(answer.get("word", [])) if kind == "DISTINGUISHABLE" else 0
    families = Counter(row["spec"]["family"] for row in history)
    outcomes = Counter(row["outcome"] for row in history)
    depths = Counter(len(row["word"]) if row["word"] is not None else 0
                     for row in history)
    sizes = Counter(row["spec"]["states"] for row in history)
    return (8 if families[spec["family"]] == 0 else 0) + \
           (10 if outcomes[kind] == 0 else 0) + \
           (6 if depths[depth] == 0 else 0) + \
           (3 if sizes[spec["states"]] == 0 else 0) + \
           (2 if families[spec["family"]] < 2 else 0)


def choose(candidates, history):
    used = {spec_id(row["spec"]) for row in history}
    remaining = [spec for spec in candidates if spec_id(spec) not in used]
    if not remaining:
        return None, None
    # Model count/semantic diversity are tie breakers. Only kernel-verified
    # historical receipts enter history; unproven hypotheses cannot reward.
    family_order = {"legacy_split": 0, "delayed_split": 1, "inert_swap": 2}
    ranked = sorted(remaining, key=lambda spec: (
        -novelty(spec, history),
        Counter(row["spec"]["family"] for row in history)[spec["family"]],
        spec["states"], family_order[spec["family"]],
        spec.get("depth", 0), spec.get("a", -1), spec.get("b", -1),
    ))
    return ranked[0], novelty(ranked[0], history)


def request_bytes(model):
    return (json.dumps(model, sort_keys=True, indent=2,
                       ensure_ascii=False) + "\n").encode("utf-8")


def checked_result(model):
    result = pf.solve(model)
    pf.validate_result(model, result)
    return result


def receipt_digests(spec):
    before, after, _, _ = model_pair(spec)
    return {
        "baseline_request_sha256": sha256(request_bytes(before)).hexdigest(),
        "candidate_request_sha256": sha256(request_bytes(after)).hexdigest(),
        "baseline_lean_sha256": sha256(
            pf.lean_source(before, checked_result(before))[0].encode("utf-8")).hexdigest(),
        "candidate_lean_sha256": sha256(
            pf.lean_source(after, checked_result(after))[0].encode("utf-8")).hexdigest(),
    }


def validate_state(root, state):
    require(type(state) is dict and set(state) == STATE_KEYS,
            "state schema mismatch")
    require(type(state["schema_version"]) is int and
            state["schema_version"] == SCHEMA, "state version mismatch")
    require(type(state["cycles"]) is list and len(state["cycles"]) <= MAX_CYCLES,
            "invalid cycle count")
    legacy_sha, legacy_seen = legacy(root)
    options = catalog(legacy_seen)
    if not state["cycles"]:
        require(state["last_utc_day"] is None and
                state["legacy_sha256"] is None,
                "empty ledger must not claim verified data")
        return legacy_sha, options
    require(state["legacy_sha256"] == legacy_sha,
            "original primitive-autonomy seed changed; review required")
    prefix, last_day, chain = [], None, ZERO_HASH
    for rec in state["cycles"]:
        require(type(rec) is dict and set(rec) == RECORD_KEYS,
                "unrecognized receipt fields")
        require(rec["status"] == STATUS, "unverified receipt cannot drive policy")
        validate_day(rec["day"])
        require(last_day is None or rec["day"] > last_day,
                "dates must strictly increase")
        last_day = rec["day"]
        require(type(rec["head_sha"]) is str and pf.HEAD.fullmatch(rec["head_sha"]),
                "invalid exact source commit")
        require(rec["legacy_sha256"] == legacy_sha,
                "receipt from a different seed")
        validate_spec(rec["spec"])
        selected, score = choose(options, prefix)
        require(rec["spec"] == selected and rec["novelty"] == score,
                "receipt was not the deterministic verified-feedback successor")
        require(rec["id"] == spec_id(rec["spec"]), "spec id mismatch")
        _, _, _, result = model_pair(rec["spec"])
        word = result.get("word")
        require(rec["outcome"] == result["kind"] and
                rec["word"] == word, "finite witness outcome drifted")
        for field, value in receipt_digests(rec["spec"]).items():
            require(rec[field] == value, "source/request digest mismatch: " + field)
        require(rec["previous_sha256"] == chain, "broken receipt chain")
        row_without_hash = {key: value for key, value in rec.items()
                            if key != "chain_sha256"}
        require(rec["chain_sha256"] == digest(row_without_hash),
                "corrupted verified receipt chain")
        chain = rec["chain_sha256"]
        prefix.append(rec)
    require(state["last_utc_day"] == last_day,
            "last day does not match final verified receipt")
    return legacy_sha, options


def plan(root, state, day, head):
    require(type(head) is str and pf.HEAD.fullmatch(head),
            "exact Git commit SHA is required")
    validate_day(day)
    legacy_sha, options = validate_state(root, state)
    last = state["last_utc_day"]
    require(last is None or day >= last, "UTC date moved backwards")
    if last == day:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "ALREADY_COMPLETED_TODAY", "day": day, "head_sha": head}
    spec, score = choose(options, state["cycles"])
    if spec is None:
        return {"schema_version": SCHEMA, "candidate": False,
                "reason": "FINITE_GRAMMAR_EXHAUSTED", "day": day, "head_sha": head}
    base, after, baseline, result = model_pair(spec)
    return {"schema_version": SCHEMA, "candidate": True,
            "day": day, "head_sha": head, "legacy_sha256": legacy_sha,
            "id": spec_id(spec), "spec": spec, "novelty": score,
            "baseline": {"model": base, "kind": baseline["kind"]},
            "candidate_model": {"model": after, "kind": result["kind"],
                                "word": result.get("word")},
            "claim_scope": "FINITE_OPERATOR_WORD_OBSERVABILITY_ONLY",
            "verification": "PENDING_LEAN_KERNEL_AND_AXIOM_AUDIT"}


def prepare(root, state_path, day, head, output):
    state = read(state_path)
    require(not output.exists() or not any(output.iterdir()),
            "output must be empty; stale evidence forbidden")
    selected = plan(root, state, day, head)
    output.mkdir(parents=True, exist_ok=True)
    if selected["candidate"]:
        paths = output / "requests"
        paths.mkdir()
        for model in (selected["baseline"]["model"],
                      selected["candidate_model"]["model"]):
            path = paths / (model["name"] + ".json")
            path.write_bytes(request_bytes(model))
            require(pf.read_request(path) == model,
                    "invalid Proof Forge finite-model request")
        pf.generate(paths, output / "proof", head)
    save(output / "plan.json", selected)
    print(json.dumps({"candidate": selected["candidate"],
                      "id": selected.get("id"),
                      "reason": selected.get("reason"),
                      "scope": "FINITE_ONLY"}))
    return selected


def validate_evidence(evidence, chosen):
    require(chosen["candidate"] is True, "no candidate receipt allowed")
    manifest = read(evidence / "proof/manifest.json")
    names = [chosen["baseline"]["model"]["name"],
             chosen["candidate_model"]["model"]["name"]]
    require(manifest["schema_version"] == 1 and
            manifest["checkout_sha"] == chosen["head_sha"] and
            set(manifest["models"]) == set(names) and
            len(manifest["models"]) == 2 and manifest["passed"] is True,
            "Lean audit manifest missing or not passed")
    digests = {}
    for role, model in (("baseline", chosen["baseline"]["model"]),
                        ("candidate", chosen["candidate_model"]["model"])):
        reqpath = evidence / "requests" / (model["name"] + ".json")
        require(reqpath.read_bytes() == request_bytes(model),
                "request differs from trusted deterministic source")
        proof = evidence / "proof" / (model["name"] + ".lean")
        result = checked_result(model)
        expected_source, theorems = pf.lean_source(model, result)
        require(proof.read_bytes() == expected_source.encode("utf-8"),
                "Lean source differs from trusted generator")
        metadata = read(evidence / "proof" / (model["name"] + ".json"))
        require(metadata["model"] == model["name"] and
                metadata["checkout_sha"] == chosen["head_sha"] and
                metadata["theorems"] == theorems and
                metadata["request_sha256"] == sha256(request_bytes(model)).hexdigest() and
                metadata["generated_lean_sha256"] ==
                sha256(expected_source.encode("utf-8")).hexdigest() and
                metadata["python_result"] == result and
                metadata["status"] == "LEAN_VERIFIED" and
                metadata["kernel_verified"] is True and
                metadata.get("axiom_audit", {}).get("passed") is True,
                "unverified source/model/axiom evidence")
        digests[role + "_request_sha256"] = metadata["request_sha256"]
        digests[role + "_lean_sha256"] = metadata["generated_lean_sha256"]
    return digests


def receipt(root, state_path, day, head, evidence, output):
    state = read(state_path)
    expected = plan(root, state, day, head)
    require(expected["candidate"], "no receipt for exhausted or repeated day")
    actual = read(evidence / "plan.json")
    require(expected == actual, "stale or tampered proposal; refuse write")
    digests = validate_evidence(evidence, expected)
    require(not output.is_symlink(), "output must not be a symlink")
    require(output != state_path or state_path.is_file(),
            "missing original state")
    status = expected["candidate_model"]
    record = {
        "id": expected["id"], "day": day, "head_sha": head,
        "legacy_sha256": expected["legacy_sha256"],
        "spec": expected["spec"], "novelty": expected["novelty"],
        "outcome": status["kind"], "word": status["word"],
        "status": STATUS,
        "previous_sha256": (
            state["cycles"][-1]["chain_sha256"] if state["cycles"] else ZERO_HASH),
        **digests,
    }
    record["chain_sha256"] = digest(record)
    updated = {**state, "legacy_sha256": expected["legacy_sha256"],
               "last_utc_day": day, "cycles": state["cycles"] + [record]}
    validate_state(root, updated)
    save(output, updated)
    print(json.dumps({"verified": record["id"], "outcome": record["outcome"],
                      "word": record["word"], "novelty": record["novelty"],
                      "cycle": len(updated["cycles"])}))
    return updated


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("prepare", "receipt"))
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--day", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--evidence", type=Path)
    args = parser.parse_args(argv)
    if args.command == "prepare":
        prepare(args.root, args.state, args.day, args.head, args.output)
    else:
        require(args.evidence is not None, "--evidence required for receipt")
        receipt(args.root, args.state, args.day, args.head,
                args.evidence, args.output)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print("PRIMITIVE_V2_ERROR: " + str(exc), file=sys.stderr)
        sys.exit(2)
