#!/usr/bin/env python3
"""Self-directed, proof-gated finite-model discovery without an LLM.

A machine-generated candidate is NEVER a theorem until the pinned Lean
kernel compiles its exact generated source and the axiom audit passes.
Verified finite observations determine which *new experiments* to propose.
The controller never mutates executable source or GitHub's main branch.

Commands:
  prepare --root DIR --state FILE --head SHA --day YYYY-MM-DD --output DIR
  receipt --root DIR --state FILE --head SHA --evidence DIR --output FILE

All source input is reviewed/pinned. State is untrusted data: never execute
a script from it. Scope is bounded finite deterministic transition systems.
"""
from __future__ import annotations

from collections import Counter
from datetime import date, timedelta
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
import argparse

from tools.autonomy import proof_forge as pf
from tools.autonomy import research_conveyor as conveyor
from tools.autonomy import research_conveyor_routes as routes

SCHEMA = 1
MAX_RECEIPTS = 96
MAX_DEPTH = 5
STATE_KEYS = {"schema_version", "catalog_sha256", "last_utc_day", "receipts"}
RECEIPT_KEYS = {
    "name", "day", "head_sha", "catalog_sha256", "seed", "parent",
    "mutation", "depth", "model", "fingerprint",
    "request_sha256", "lean_sha256", "outcome", "word", "status",
    "previous_sha256", "chain_sha256", "comparison"
}
VALID_ID = re.compile(r"fd_[a-f0-9]{16}\Z")
VALID_64 = re.compile(r"[0-9a-f]{64}\Z")
SEED_ORDER = ("observer", "laakso", "siphon", "observer_hidden")
SOURCE_SIPHON_BLOB = "1dcff20f3aec8d580273bcc2b5097ed75fe93184"
STATUS = "LEAN_VERIFIED_FINITE_ONLY"
SOURCE_SCOPE = "REVIEWED_FINITE_STATE_INTERPRETATION_ONLY"


def demand(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


def digest(obj):
    return sha256(canonical(obj)).hexdigest()


def save(path: Path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, sort_keys=True, indent=2,
                               ensure_ascii=False) + "\n", encoding="utf-8")


def load(path: Path):
    demand(path.is_file() and not path.is_symlink(), "state/evidence file must exist as a regular file")
    demand(path.stat().st_size <= 500_000, "state/evidence file exceeds input bound")
    return json.loads(path.read_text("utf-8"),
                      object_pairs_hook=pf.object_no_duplicates)


def utc_day(day):
    demand(isinstance(day, str) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", day),
           "invalid UTC day")
    demand(date.fromisoformat(day).isoformat() == day,
           "non-calendar UTC day")
    return day


def empty_state():
    return {"schema_version": SCHEMA, "catalog_sha256": None,
            "last_utc_day": None, "receipts": []}


def model_fingerprint(model):
    return digest({"observations": model["observations"],
                   "transitions": model["transitions"],
                   "pair": model["pair"]})


def rename_model(model):
    fingerprint = model_fingerprint(model)
    obj = dict(model)
    obj["name"] = "fd_" + fingerprint[:16]
    return obj


def normalize_labels(values):
    labels, out = {}, []
    for val in values:
        if val not in labels:
            labels[val] = len(labels)
        out.append(labels[val])
    return out


def validate_model(model):
    demand(type(model) is dict and set(model) == {
        "schema_version", "name", "observations", "transitions", "pair"
    }, "invalid proof model fields")
    demand(model["schema_version"] == 1 and type(model["schema_version"]) is int,
           "model schema invalid")
    name = model["name"]
    demand(type(name) is str and VALID_ID.fullmatch(name), "unapproved finite model name")
    demand(2 <= len(model["observations"]) <= pf.MAX_STATES,
           "invalid state count")
    n = len(model["observations"])
    demand(type(model["transitions"]) is list
           and 1 <= len(model["transitions"]) <= pf.MAX_ACTIONS,
           "invalid action count")
    for val in model["observations"]:
        demand(type(val) is int and 0 <= val < pf.MAX_OBSERVATIONS,
               "observation outside finite alphabet")
    for row in model["transitions"]:
        demand(type(row) is list and len(row) == n
               and all(type(i) is int and 0 <= i < n for i in row),
               "transition is not total deterministic finite function")
    demand(type(model["pair"]) is list and len(model["pair"]) == 2
           and all(type(i) is int and 0 <= i < n for i in model["pair"]),
           "invalid initial state pair")
    demand(rename_model(model) == model, "noncanonical model identifier")
    return model


def seeds(root: Path):
    """Exactly reviewed and byte-pinned initial interpretations, not guesses."""
    refs = {
        "observer": routes.source_anchor(root, "observer"),
        "laakso": routes.source_anchor(root, "laakso"),
    }
    siphon_path = root / conveyor.SOURCE
    demand(siphon_path.is_file() and not siphon_path.is_symlink(),
           "reviewed Siphon note missing")
    demand(routes.git_blob_sha(siphon_path.read_bytes()) == SOURCE_SIPHON_BLOB,
           "Siphon source semantics changed; adapter requires review")
    refs["siphon"] = conveyor.discover_lead(root)
    sources = {
        "observer": routes.observer_model(root, "observer_primitive"),
        "laakso": routes.laakso_model("laakso_w1_advance"),
        "siphon": conveyor.model(0, "old"),
        "observer_hidden": routes.observer_model(root, "observer_hidden"),
    }
    records = []
    for seed in SEED_ORDER:
        model = rename_model(sources[seed])
        validate_model(model)
        records.append({"seed": seed, "model": model,
                        "source_sha256": refs["observer" if seed == "observer_hidden"
                                             else seed]["source_sha256"]})
    catalog = digest({"seed_models": records,
                      "source_refs": refs,
                      "source_siphon_git_blob": SOURCE_SIPHON_BLOB,
                      "adapter_version": 1})
    return catalog, records


def observational_partition(model):
    """Greatest future-observation congruence, via finite partition refinement.

    This is a Python calculation used to construct a quotient candidate.
    It is not counted as a Lean proof of the generic quotient theorem.
    """
    n = len(model["observations"])
    blocks = normalize_labels(model["observations"])
    for _ in range(n + 1):
        sig = [(model["observations"][i],
                *(blocks[row[i]] for row in model["transitions"]))
               for i in range(n)]
        nxt = normalize_labels(sig)
        if nxt == blocks:
            for row in model["transitions"]:
                for i in range(n):
                    for j in range(n):
                        if blocks[i] == blocks[j]:
                            demand(blocks[row[i]] == blocks[row[j]],
                                   "partition is not congruent")
            return blocks
        blocks = nxt
    raise ValueError("partition refinement did not stabilize")


def quotient(model):
    blocks = observational_partition(model)
    qn = max(blocks) + 1
    if qn < 2 or qn >= len(blocks):
        return None
    representatives = [blocks.index(i) for i in range(qn)]
    rows = [[blocks[row[rep]] for rep in representatives]
            for row in model["transitions"]]
    observations = normalize_labels([
        model["observations"][r] for r in representatives
    ])
    return {"schema_version": 1, "name": "placeholder",
            "observations": observations, "transitions": rows,
            "pair": [blocks[i] for i in model["pair"]]}


def mutate(model, outcome):
    """Fixed small grammar; prior verified result determines applicable rules."""
    n = len(model["observations"])
    actions = model["transitions"]
    obs = model["observations"]
    left, right = model["pair"]

    def change(name, *, observations=None, transitions=None, pair=None):
        candidate = {"schema_version": 1, "name": "placeholder",
                     "observations": (obs if observations is None else observations)[:],
                     "transitions": [row[:] for row in
                                     (actions if transitions is None else transitions)],
                     "pair": (model["pair"] if pair is None else pair)[:]}
        return name, candidate

    # Reduction is often more informative than an arbitrary new example.
    reduced = quotient(model)
    if reduced is not None:
        yield "bisimulation_quotient", reduced

    if outcome == "DISTINGUISHABLE":
        if len(actions) < pf.MAX_ACTIONS:
            squared = [actions[0][actions[0][i]] for i in range(n)]
            if squared not in actions:
                yield change("compose_first_action",
                             transitions=actions + [squared])
        if len(set(obs)) > 1:
            collapsed = [0 if v == max(obs) else v for v in obs]
            if collapsed != obs:
                yield change("forget_last_observation",
                             observations=normalize_labels(collapsed))
        if len(actions) > 1:
            yield change("remove_last_action", transitions=actions[:-1])
    else:
        if obs[left] == obs[right] and left != right:
            if max(obs) < pf.MAX_OBSERVATIONS - 1:
                lifted = obs[:]
                lifted[right] = max(obs) + 1
                yield change("split_hidden_readout", observations=lifted)
            if len(actions) < pf.MAX_ACTIONS and len(set(obs)) > 1:
                target = next((i for i in range(n) if obs[i] != obs[left]), None)
                if target is not None:
                    probe = list(range(n))
                    probe[right] = target
                    if probe not in actions:
                        yield change("append_distinguishing_probe",
                                     transitions=actions + [probe])
        if n <= pf.MAX_STATES // 2:
            extended_actions = [
                [row[i % n] + n * (i // n) for i in range(2*n)]
                for row in actions
            ]
            yield change("duplicate_hidden_sheet",
                         observations=obs * 2, transitions=extended_actions,
                         pair=[left, left+n])

    # Deliberate one-entry perturbation tests robustness of observational law.
    mutated = [row[:] for row in actions]
    mutated[0][right] = (mutated[0][right] + 1) % n
    if mutated != actions:
        yield change("perturb_one_transition", transitions=mutated)

    # Change which initially identical visible states are compared.
    options = [(i, j) for i in range(n) for j in range(i+1, n)
               if obs[i] == obs[j] and [i,j] != model["pair"]]
    if options:
        yield change("change_observer_pair", pair=list(options[0]))

    # Gradually enlarge a finite state space, but never invent continuous laws.
    if n < pf.MAX_STATES:
        new_actions = [row + [n] for row in actions]
        yield change("adjoin_absorbing_state",
                     observations=obs+[obs[left]],
                     transitions=new_actions, pair=[left,n])


def propose(root: Path, state):
    """Deterministic breadth-first scientific model search with domain balance."""
    catalog, roots = seeds(root)
    if state["catalog_sha256"] is not None:
        demand(state["catalog_sha256"] == catalog,
               "reviewed source catalog changed; stop before new proof")
    seen = {r["fingerprint"] for r in state["receipts"]}
    counts = Counter(r["seed"] for r in state["receipts"])
    options, offered = [], set()
    for n, seed in enumerate(roots):
        m = seed["model"]
        fp = model_fingerprint(m)
        if fp not in seen:
            options.append(((0, counts[seed["seed"]], n),
                            {"seed": seed["seed"], "parent": None,
                             "depth": 0, "mutation": "reviewed_seed",
                             "model": m, "fingerprint": fp}))
            offered.add(fp)

    for i, record in enumerate(state["receipts"]):
        if record["depth"] >= MAX_DEPTH:
            continue
        for rank, (operation, raw_model) in enumerate(
            mutate(record["model"], record["outcome"])
        ):
            proposed = rename_model(raw_model)
            validate_model(proposed)
            fp = model_fingerprint(proposed)
            if fp in seen or fp in offered:
                continue
            offered.add(fp)
            seed = record["seed"]
            option = {"seed": seed,
                      "parent": record["name"], "depth": record["depth"]+1,
                      "mutation": operation, "model": proposed,
                      "fingerprint": fp}
            # Preserve several research families instead of exploring only
            # the largest or easiest branch. Depth first prioritizes breadth.
            rank_key = (1, counts[seed], record["depth"], rank, i, fp)
            options.append((rank_key, option))
    if not options:
        return None, catalog
    _, selected = min(options, key=lambda row: row[0])
    return selected, catalog


def validate_state(root: Path, state):
    demand(type(state) is dict and set(state) == STATE_KEYS,
           "invalid persistent state shape")
    demand(type(state["schema_version"]) is int and state["schema_version"] == SCHEMA,
           "unsupported state schema version")
    demand(type(state["receipts"]) is list
           and len(state["receipts"]) <= MAX_RECEIPTS,
           "verified receipt budget exceeded")
    catalog, _ = seeds(root)
    if state["catalog_sha256"] is not None:
        demand(type(state["catalog_sha256"]) is str
               and bool(VALID_64.fullmatch(state["catalog_sha256"]))
               and state["catalog_sha256"] == catalog,
               "reviewed catalog mismatch")
    if not state["receipts"]:
        demand(state["catalog_sha256"] is None
               and state["last_utc_day"] is None,
               "empty ledger must not claim prior work")
        return state
    demand(state["catalog_sha256"] == catalog,
           "verified history missing reviewed catalog SHA")
    seen, last, previous_chain = set(), None, "0" * 64
    for r in state["receipts"]:
        demand(type(r) is dict and set(r) == RECEIPT_KEYS,
               "malformed verified receipt")
        demand(type(r["name"]) is str and VALID_ID.fullmatch(r["name"]),
               "invalid receipt name")
        demand(r["name"] not in seen, "duplicate finite experiment")
        seen.add(r["name"])
        model = validate_model(r["model"])
        demand(r["name"] == model["name"]
               and r["fingerprint"] == model_fingerprint(model),
               "model fingerprint mismatch")
        demand(r["seed"] in SEED_ORDER and r["depth"] in range(MAX_DEPTH+1),
               "invalid derivation depth or seed")
        demand(r["parent"] is None or
               (r["parent"] in seen and r["parent"] != r["name"]),
               "parent receipt missing or future")
        demand((r["parent"] is None) == (r["depth"] == 0),
               "incorrect parent/depth structure")
        demand(r["outcome"] in ("DISTINGUISHABLE", "EQUIVALENT")
               and r["status"] == STATUS,
               "unverified or unsupported finite result")
        solved = pf.solve(model)
        pf.validate_result(model, solved)
        demand(r["outcome"] == solved["kind"] and
               r["word"] == solved.get("word"),
               "receipt outcome not equal to independently reconstructed finite solve")
        demand(type(r["head_sha"]) is str and pf.HEAD.fullmatch(r["head_sha"]),
               "invalid main commit SHA in receipt")
        utc_day(r["day"])
        demand(last is None or last < r["day"], "nonmonotone UTC verification days")
        last = r["day"]
        for key in ("request_sha256", "lean_sha256", "catalog_sha256",
                    "previous_sha256", "chain_sha256"):
            demand(type(r[key]) is str and VALID_64.fullmatch(r[key]),
                   "missing receipt hash " + key)
        demand(r["catalog_sha256"] == catalog and
               r["previous_sha256"] == previous_chain,
               "broken chain or source identity")
        body = {key:value for key,value in r.items() if key != "chain_sha256"}
        demand(r["chain_sha256"] == digest(body),
               "tampered verified receipt hash chain")
        demand(type(r["comparison"]) is str and len(r["comparison"]) <= 100,
               "invalid comparison classification")
        previous_chain = r["chain_sha256"]
    demand(state["last_utc_day"] == last,
           "last verified UTC day does not match receipt history")
    return state


def plan(root, state, head, day):
    demand(type(head) is str and pf.HEAD.fullmatch(head),
           "exact 40-character source commit required")
    utc_day(day)
    validate_state(root, state)
    if state["last_utc_day"] is not None:
        demand(day >= state["last_utc_day"], "UTC day is older than last proof")
    if state["last_utc_day"] == day:
        return {"schema_version":1, "candidate":False,
                "reason":"ALREADY_VERIFIED_TODAY", "main_sha":head, "day":day}
    if len(state["receipts"]) >= MAX_RECEIPTS:
        return {"schema_version":1, "candidate":False,
                "reason":"VERIFIED_DISCOVERY_BUDGET_EXHAUSTED", "main_sha":head,
                "day":day}
    candidate, catalog = propose(root, state)
    if candidate is None:
        return {"schema_version":1, "candidate":False,
                "reason":"FINITE_SEARCH_SPACE_EXHAUSTED", "main_sha":head,
                "day":day}
    predicted = pf.solve(candidate["model"])
    pf.validate_result(candidate["model"], predicted)
    return {
        "schema_version":1,
        "candidate":True,
        "catalog_sha256":catalog, "main_sha":head, "day":day,
        **candidate,
        "hypothesis":"PARENT_KIND_PRESERVED_FOR_THIS_STATE_PAIR"
        if candidate["parent"] else "FIRST_REVIEWED_FINITE_CASE",
        "python_observation": {"kind":predicted["kind"],
                               "word":predicted.get("word"),
                               "proof_status":"PENDING_KERNEL_VERIFICATION"},
        "scope": SOURCE_SCOPE,
    }


def prepare(root, state_file, head, day, output):
    state = validate_state(root, load(state_file))
    demand(not output.exists() or not any(output.iterdir()),
           "output directory must begin empty")
    chosen = plan(root, state, head, day)
    output.mkdir(parents=True, exist_ok=True)
    if chosen["candidate"]:
        name = chosen["model"]["name"]
        requests = output / "requests"
        requests.mkdir()
        save(requests / (name+".json"), chosen["model"])
        demand(pf.read_request(requests / (name+".json")) == chosen["model"],
               "generated JSON does not pass Proof Forge validation")
        pf.generate(requests, output / "proof", head)
    save(output / "plan.json", chosen)
    print(json.dumps({"candidate":chosen["candidate"],
                      "task":chosen.get("model", {}).get("name"),
                      "seed":chosen.get("seed"),
                      "mutation":chosen.get("mutation"),
                      "status":"UNVERIFIED_FINITE_CANDIDATE" if chosen["candidate"]
                      else chosen["reason"]}))
    return chosen


def receipt(root, state_file, head, evidence, output):
    state = validate_state(root, load(state_file))
    given = load(evidence / "plan.json")
    demand(given.get("candidate") is True, "no finite task to certify")
    expected = plan(root, state, head, given.get("day"))
    demand(given == expected and expected["candidate"],
           "stale or modified finite candidate")
    m = expected["model"]
    name = m["name"]
    path = evidence / "requests" / (name+".json")
    demand(pf.read_request(path) == m, "changed requested finite model")
    demand(pf.audit(evidence / "proof") == 0,
           "exact finite Lean kernel evidence did not pass audit")
    manifest = load(evidence / "proof/manifest.json")
    report = load(evidence / "proof" / (name + ".json"))
    demand(manifest.get("models") == [name] and
           manifest.get("checkout_sha") == head and
           manifest.get("passed") is True,
           "complete exact-head Lean manifest required")
    solved = pf.solve(m)
    pf.validate_result(m, solved)
    lean_source, theorem_names = pf.lean_source(m, solved)
    generated = evidence / "proof" / (name + ".lean")
    demand(generated.is_file() and not generated.is_symlink() and
           generated.read_bytes() == lean_source.encode("utf-8"),
           "Lean file is not exact deterministic proof-generator output")
    demand(report.get("model") == name and report.get("checkout_sha") == head
           and report.get("status") == "LEAN_VERIFIED"
           and report.get("kernel_verified") is True
           and report.get("axiom_audit", {}).get("passed") is True,
           "actual Lean kernel and approved axioms are required")
    demand(report.get("theorems") == theorem_names and
           report.get("python_result") == solved and
           report.get("generated_lean_sha256") == sha256(generated.read_bytes()).hexdigest()
           and report.get("request_sha256") == sha256(path.read_bytes()).hexdigest(),
           "verified artifact content differs from deterministic candidate")
    exit_file = evidence / "proof" / (name + ".exit")
    demand(exit_file.is_file() and exit_file.read_text("utf-8").strip() == "0",
           "Lean compiler did not exit zero")
    # Consume a fully checked outcome. Do not trust user-provided summaries.
    parent = next((r for r in state["receipts"] if r["name"] == expected["parent"]), None)
    if parent is None:
        classification = "NEW_REVIEWED_SEED_FINITE_ONLY"
    elif parent["outcome"] != solved["kind"]:
        classification = "FINITE_PAIR_BEHAVIOR_CHANGED"
    elif (parent["outcome"] == "DISTINGUISHABLE" and
          len(parent["word"]) != len(solved.get("word", []))):
        classification = "FINITE_SHORTEST_DEPTH_CHANGED"
    else:
        classification = "FINITE_PAIR_BEHAVIOR_PRESERVED"
    prev = (state["receipts"][-1]["chain_sha256"]
            if state["receipts"] else "0" * 64)
    entry = {
        "name":name, "day":expected["day"], "head_sha":head,
        "catalog_sha256":expected["catalog_sha256"],
        "seed":expected["seed"], "parent":expected["parent"],
        "mutation":expected["mutation"], "depth":expected["depth"],
        "model":m, "fingerprint":expected["fingerprint"],
        "request_sha256":report["request_sha256"],
        "lean_sha256":report["generated_lean_sha256"],
        "outcome":solved["kind"], "word":solved.get("word"),
        "status":STATUS,
        "previous_sha256":prev,
        "comparison":classification,
    }
    entry["chain_sha256"] = digest(entry)
    state["receipts"].append(entry)
    state["catalog_sha256"] = expected["catalog_sha256"]
    state["last_utc_day"] = expected["day"]
    validate_state(root, state)
    save(output, state)
    followup_day = (date.fromisoformat(expected["day"]) +
                    timedelta(days=1)).isoformat()
    followup = plan(root, state, head, followup_day)
    print(json.dumps({"verified":name, "outcome":solved["kind"],
                      "comparison":classification,
                      "total":len(state["receipts"]),
                      "next_mutation":followup.get("mutation"),
                      "next_domain":followup.get("seed")}))
    return entry


def main(argv=None):
    arg = argparse.ArgumentParser(description=__doc__)
    group = arg.add_subparsers(dest="mode", required=True)
    for mode in ("prepare", "receipt"):
        p = group.add_parser(mode)
        p.add_argument("--root", type=Path, required=True)
        p.add_argument("--state", type=Path, required=True)
        p.add_argument("--head", required=True)
        p.add_argument("--output", type=Path, required=True)
        if mode == "prepare":
            p.add_argument("--day", required=True)
        else:
            p.add_argument("--evidence", type=Path, required=True)
    args = arg.parse_args(argv)
    try:
        if args.mode == "prepare":
            prepare(args.root.resolve(), args.state, args.head, args.day, args.output)
        else:
            receipt(args.root.resolve(), args.state, args.head, args.evidence, args.output)
    except (ValueError, KeyError, TypeError, OSError,
            UnicodeError, json.JSONDecodeError) as exc:
        print("FINITE_DISCOVERY_FAIL_CLOSED:", str(exc), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
