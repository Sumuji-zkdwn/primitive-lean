#!/usr/bin/env python3
"""Reviewed finite research adapters for Research Conveyor.

These are finite, source-bound *interpretations*. They do not derive an
arbitrary dynamical law from natural-language notes. Keep model adaptation,
source provenance and outcome-driven routing separate from the Lean verifier.

The historical Siphon adapter remains in research_conveyor.py, unchanged.
"""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path

from tools.autonomy import proof_forge

# Published names are the on-disk Proof Forge request names (<= 49 chars).
OBSERVER = ("observer_primitive", "observer_macro",
            "observer_hidden", "observer_visible")
LAAKSO = ("laakso_w1_stop", "laakso_w1_advance", "laakso_w2_advance")
SIPHON = tuple(f"siphon_z3_u{u}_{kind}"
               for u in range(3) for kind in ("old", "fresh"))
ALL_IDS = frozenset((*SIPHON, *OBSERVER, *LAAKSO))
ROUTE_ORDER = ("siphon", "observer", "laakso")
SOURCE_SPECS = {
    "observer": {
        "path": "docs/research/2026-11-11-observer-orientation-depth.md",
        "required": ("leastDepth", "four-state counterexample", "macro",
                     "observational", "Fin 3"),
        "anchor": "A four-state counterexample",
        "scope": "FINITE_OPERATOR_WORD_MODEL_ONLY",
        "label": "REVIEWED_OBSERVER_SOURCE_ANCHOR",
    },
    "laakso": {
        "path": "docs/research/2026-11-17-laakso-bonding-audit.md",
        "required": ("RawVertex (Fin 2) (Fin 1)", "rawProjection",
                     "advanceRightGeneral", "W1", "W2"),
        "anchor": "W1の古い頂点コピー",
        "scope": "FINITE_LAAKSO_RAW_VERTEX_ONLY",
        "label": "REVIEWED_LAAKSO_SOURCE_ANCHOR",
    },
}
SCOPE = {"siphon": "FINITE_Z3_MODEL_ONLY",
         **{name: spec["scope"] for name, spec in SOURCE_SPECS.items()}}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def route_of(task_id: str) -> str:
    require(type(task_id) is str and task_id in ALL_IDS,
            "task is not in the reviewed finite adapter registry")
    if task_id.startswith("siphon_z3_"):
        return "siphon"
    if task_id in OBSERVER:
        return "observer"
    return "laakso"


def source_anchor(root: Path, route: str) -> dict:
    """Source bytes and an exact reviewed line, never executable instructions."""
    require(route in SOURCE_SPECS, "unreviewed research route")
    spec = SOURCE_SPECS[route]
    path = root / spec["path"]
    require(path.is_file() and not path.is_symlink(), "research source unavailable")
    data = path.read_bytes()
    require(len(data) <= 300_000, "research source too large")
    source = data.decode("utf-8")
    require(all(item in source for item in spec["required"]),
            "reviewed model source semantics changed")
    hits = [(n, " ".join(line.split())) for n, line in
            enumerate(source.splitlines(), 1) if spec["anchor"] in line]
    require(len(hits) == 1 and len(hits[0][1]) <= 360,
            "expected unique source anchor line missing")
    lineno, evidence = hits[0]
    digest = sha256(data).hexdigest()
    ident = sha256((spec["path"] + "\0" + evidence).encode("utf-8")).hexdigest()[:20]
    return {"id": ident, "path": spec["path"], "line": lineno,
            "evidence": evidence, "source_sha256": digest,
            "priority": 0, "status": spec["label"]}


def _four_state(root):
    """Check against the already-reviewed and kernel-certified examples."""
    base = root / "proof_forge/requests"
    old = proof_forge.read_request(base / "orientation_primitive.json")
    macro = proof_forge.read_request(base / "orientation_macro.json")
    require(old["observations"] == [0, 0, 0, 1]
            and old["transitions"] == [[0, 2, 3, 3]]
            and old["pair"] == [0, 1], "primitive reference fixture changed")
    step = old["transitions"][0]
    require(macro["observations"] == old["observations"] and
            macro["transitions"] == [step, [step[step[i]] for i in range(4)]] and
            macro["pair"] == [0, 1], "macro reference fixture changed")
    return old, macro


def _eight_state(root):
    base = root / "proof_forge/requests"
    hidden = proof_forge.read_request(base / "orientation_hidden_quotient.json")
    old, macro = _four_state(root)
    step, compiled = macro["transitions"]
    expected_a = [step[i % 4] + 4 * (i // 4) for i in range(8)]
    expected_b = [compiled[i % 4] + 4 * (i // 4) for i in range(8)]
    require(hidden["observations"] == old["observations"] * 2
            and hidden["transitions"] == [expected_a, expected_b]
            and hidden["pair"] == [0, 4], "hidden-state reference fixture changed")
    return hidden


def observer_model(root: Path, task_id: str) -> dict:
    require(task_id in OBSERVER, "not an observer adapter task")
    old, macro = _four_state(root)
    if task_id == "observer_primitive":
        model = old
    elif task_id == "observer_macro":
        model = macro
    else:
        model = _eight_state(root)
        if task_id == "observer_visible":
            # A *new readout*, not an alleged new dynamical operation.
            # Hidden bit h is now part of the observable: K=(old K,h).
            model["observations"] = [v + (2 if i >= 4 else 0)
                                      for i, v in enumerate(model["observations"])]
    return {**model, "name": task_id}


def laakso_model(task_id: str) -> dict:
    """Actual first-level RawVertex(G0) (8 states), with rawProjection readout.

    Encoding: old L0,L1,R0,R1, W1 sheet0/1, W2 sheet0/1.
    Original advanceRightGeneral base fixes old vertices, W1->W2,
    W2->right endpoint on the same sheet. An extra explicit identity
    operation is a *stipulated inert control*, not a claim about a
    continuous Laakso-space flow or upper-level dynamics.
    """
    require(task_id in LAAKSO, "not a Laakso raw-vertex task")
    readout = [0, 1, 2, 3, 4, 4, 5, 5]
    stop = list(range(8))
    advance = [0, 1, 2, 3, 6, 7, 2, 3]
    return {
        "schema_version": 1,
        "name": task_id,
        "observations": readout,
        "transitions": [stop] if task_id == "laakso_w1_stop"
                       else [stop, advance],
        "pair": [6, 7] if task_id == "laakso_w2_advance" else [4, 5],
    }


def source_model(root: Path, task_id: str):
    route = route_of(task_id)
    if route == "observer":
        return observer_model(root, task_id)
    if route == "laakso":
        return laakso_model(task_id)
    raise ValueError("legacy Siphon model belongs to the existing adapter")


def next_in_route(state: dict, route: str):
    """A strictly bounded finite search with conditional branch decisions."""
    completed = {r["task_id"]: r for r in state["results"]}
    def has(name):
        return name in completed
    def is_expected(name, kind, word=None):
        row = completed.get(name)
        return row is not None and row["kind"] == kind and (
            kind == "EQUIVALENT" or row.get("shortest_word") == word)
    if route == "siphon":
        for u in range(3):
            old = f"siphon_z3_u{u}_old"
            new = f"siphon_z3_u{u}_fresh"
            if not has(old):
                return old
            if is_expected(old, "EQUIVALENT") and not has(new):
                return new
        return None
    if route == "observer":
        if not has("observer_primitive"):
            return "observer_primitive"
        if (is_expected("observer_primitive", "DISTINGUISHABLE", [0,0])
                and not has("observer_macro")):
            return "observer_macro"
        if not has("observer_hidden"):
            return "observer_hidden"
        if is_expected("observer_hidden", "EQUIVALENT") and not has("observer_visible"):
            return "observer_visible"
        return None
    if route == "laakso":
        if not has("laakso_w1_stop"):
            return "laakso_w1_stop"
        if is_expected("laakso_w1_stop", "EQUIVALENT") and not has("laakso_w1_advance"):
            return "laakso_w1_advance"
        if not has("laakso_w2_advance"):
            return "laakso_w2_advance"
        return None
    raise ValueError("unknown route")


def choose_next(state: dict):
    """Balanced scheduling: fewest completed proofs first; stable tie order.

    Legacy persistent results count toward the Siphon family. This is
    deterministically replayable and creates no new tasks without a
    kernel-verified predecessor receipt.
    """
    candidates = []
    for priority, route in enumerate(ROUTE_ORDER):
        task_id = next_in_route(state, route)
        if task_id is not None:
            completed = sum(route_of(row["task_id"]) == route for row in state["results"])
            candidates.append((completed, priority, route, task_id))
    if not candidates:
        return None
    _, _, route, task_id = min(candidates)
    return route, task_id


def scope(task_id):
    return SCOPE[route_of(task_id)]
