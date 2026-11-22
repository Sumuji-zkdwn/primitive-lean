#!/usr/bin/env python3
"""Bounded finite-observer model checker that emits Lean kernel-checkable certificates.

This tool does not call an AI API or execute request-provided code. JSON requests
are data, and the only Lean emitted is generated from validated small integers.
A Python conclusion is NOT called proved until the generated Lean compiles at
--trust=0 and its theorem axioms have been audited.

Usage:
  python tools/autonomy/proof_forge.py generate --requests proof_forge/requests \
      --output verification/proof-forge --head <exact-40-char-commit-sha>
  python tools/autonomy/proof_forge.py audit --output verification/proof-forge
"""
from __future__ import annotations

import argparse
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

MAX_FILES = 12
MAX_BYTES = 8192
MAX_STATES = 12
MAX_ACTIONS = 4
MAX_OBSERVATIONS = 8
NAME = re.compile(r"[a-z][a-z0-9_-]{1,48}\Z")
HEAD = re.compile(r"[0-9a-f]{40}\Z")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require_int(value, low, high, label):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{label}: expected integer in [{low}, {high}]")
    return value


def object_no_duplicates(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"duplicate JSON field: {key}")
        obj[key] = value
    return obj


def read_request(path: Path) -> dict:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"not a regular request file: {path.name}")
    data = path.read_bytes()
    if len(data) > MAX_BYTES:
        raise ValueError(f"request too large: {path.name}")
    obj = json.loads(data.decode("utf-8"), object_pairs_hook=object_no_duplicates)
    if type(obj) is not dict or set(obj) != {
        "schema_version", "name", "observations", "transitions", "pair"
    }:
        raise ValueError("request must have exactly the five documented fields")
    if obj["schema_version"] != 1 or type(obj["schema_version"]) is not int:
        raise ValueError("unsupported request schema")
    name = obj["name"]
    if not isinstance(name, str) or not NAME.fullmatch(name) or path.stem != name:
        raise ValueError(f"invalid name/file stem: {name!r}")
    observations = obj["observations"]
    if type(observations) is not list or not 2 <= len(observations) <= MAX_STATES:
        raise ValueError("observations must define 2..12 states")
    n = len(observations)
    for i, value in enumerate(observations):
        require_int(value, 0, MAX_OBSERVATIONS - 1, f"observations[{i}]")
    transitions = obj["transitions"]
    if type(transitions) is not list or not 1 <= len(transitions) <= MAX_ACTIONS:
        raise ValueError("transitions must provide 1..4 total action rows")
    for a, row in enumerate(transitions):
        if type(row) is not list or len(row) != n:
            raise ValueError(f"action {a} must have {n} destinations")
        for s, value in enumerate(row):
            require_int(value, 0, n - 1, f"transitions[{a}][{s}]")
    pair = obj["pair"]
    if type(pair) is not list or len(pair) != 2:
        raise ValueError("pair must be a two-element state list")
    for i, value in enumerate(pair):
        require_int(value, 0, n - 1, f"pair[{i}]")
    return obj


def advance(model: dict, state: int, word: tuple[int, ...]) -> int:
    for action in word:
        state = model["transitions"][action][state]
    return state


def solve(model: dict) -> dict:
    """BFS on the product automaton; absence of a witness is exhaustive."""
    left, right = model["pair"]
    seen: dict[tuple[int, int], tuple[int, ...]] = {(left, right): ()}
    pending = deque([(left, right)])
    while pending:
        x, y = pending.popleft()
        word = seen[(x, y)]
        if model["observations"][x] != model["observations"][y]:
            return {"kind": "DISTINGUISHABLE", "word": list(word),
                    "reachable_pairs": len(seen), "states_at_witness": [x, y]}
        for action, row in enumerate(model["transitions"]):
            nxt = (row[x], row[y])
            if nxt not in seen:
                seen[nxt] = word + (action,)
                pending.append(nxt)
    # The computed relation contains the initial pair, is observation preserving
    # and is closed under every action. Lean checks all three properties below.
    return {"kind": "EQUIVALENT", "reachable_pairs": len(seen),
            "pairs": [list(pair) for pair in seen]}


def validate_result(model: dict, result: dict) -> None:
    """Independent finite sanity checks, not a substitute for Lean."""
    x0, y0 = model["pair"]
    if result["kind"] == "DISTINGUISHABLE":
        word = tuple(result["word"])
        x, y = advance(model, x0, word), advance(model, y0, word)
        if model["observations"][x] == model["observations"][y]:
            raise ValueError("invalid distinguishing witness")
        # Enumerate exactly the reachable pairs of every shorter length.
        layer = {(x0, y0)}
        for _ in range(len(word)):
            if any(model["observations"][x] != model["observations"][y]
                   for x, y in layer):
                raise ValueError("witness was not shortest")
            layer = {(row[x], row[y]) for x, y in layer
                     for row in model["transitions"]}
    else:
        pairs = {tuple(pair) for pair in result["pairs"]}
        if (x0, y0) not in pairs:
            raise ValueError("missing initial pair")
        for x, y in pairs:
            if model["observations"][x] != model["observations"][y]:
                raise ValueError("invariant has differing observations")
            for row in model["transitions"]:
                if (row[x], row[y]) not in pairs:
                    raise ValueError("invariant is not action-closed")


def ite(field: str, values: list[int], typ: str) -> str:
    expr = f"({values[-1]} : {typ})"
    for i in reversed(range(len(values) - 1)):
        expr = f"if {field} = {i} then ({values[i]} : {typ}) else ({expr})"
    return expr


def lean_source(model: dict, result: dict) -> tuple[str, list[str]]:
    n = len(model["observations"])
    m = len(model["transitions"])
    o = max(model["observations"]) + 1
    namespace = "ProofForge_" + model["name"].replace("-", "_")
    x, y = model["pair"]
    rows = [ite("s.val", row, "State") for row in model["transitions"]]
    step_expr = ite_actions(rows)
    lines = [
        "import Mathlib.Tactic",
        "",
        "/- Generated exclusively from bounded integer JSON, not from model output.",
        "   No result is accepted before trust=0 compilation and axiom audit. -/",
        f"namespace {namespace}",
        f"abbrev State := Fin {n}",
        f"abbrev Action := Fin {m}",
        f"abbrev Observation := Fin {o}",
        f"def readout (s : State) : Observation := {ite('s.val', model['observations'], 'Observation')}",
        f"def step (a : Action) (s : State) : State := {step_expr}",
        "def run : List Action → State → State",
        "  | [], s => s",
        "  | a :: tail, s => run tail (step a s)",
        f"def originLeft : State := {x}",
        f"def originRight : State := {y}",
        "",
    ]
    if result["kind"] == "DISTINGUISHABLE":
        word = result["word"]
        witness = "[" + ", ".join(str(a) for a in word) + "]"
        lines.extend([
            f"def witness : List Action := {witness}",
            "theorem word_separates :",
            "    readout (run witness originLeft) ≠ readout (run witness originRight) := by",
            "  decide",
            "",
            "/-- Equality for every word up to the supplied depth, not just sampled words. -/",
            "def agreeUpTo : Nat → State → State → Prop",
            "  | 0, u, v => readout u = readout v",
            "  | d + 1, u, v =>",
            "      readout u = readout v ∧",
            "      ∀ a : Action, agreeUpTo d (step a u) (step a v)",
            "",
            "theorem agreeUpTo_sound :",
            "    ∀ (fuel : Nat) (u v : State), agreeUpTo fuel u v →",
            "      ∀ w : List Action, w.length ≤ fuel →",
            "        readout (run w u) = readout (run w v) := by",
            "  intro fuel",
            "  induction fuel with",
            "  | zero =>",
            "      intro u v h w hw",
            "      cases w with",
            "      | nil => exact h",
            "      | cons a tail => simp at hw",
            "  | succ fuel ih =>",
            "      intro u v h w hw",
            "      cases w with",
            "      | nil => exact h.1",
            "      | cons a tail =>",
            "          have ht : tail.length ≤ fuel := by",
            "            simp only [List.length_cons] at hw",
            "            omega",
            "          change readout (run tail (step a u)) =",
            "            readout (run tail (step a v))",
            "          exact ih (step a u) (step a v) (h.2 a) tail ht",
            "",
            "theorem no_shorter_word (w : List Action)",
            f"    (h : w.length < {len(word)}) :",
            "    readout (run w originLeft) = readout (run w originRight) := by",
        ])
        if len(word) == 0:
            lines.append("  omega")
        else:
            lines.extend([
                f"  have checked : agreeUpTo {len(word) - 1} originLeft originRight := by decide",
                f"  exact agreeUpTo_sound {len(word) - 1} originLeft originRight checked w (by omega)",
            ])
        theorems = ["word_separates", "agreeUpTo_sound", "no_shorter_word"]
    else:
        literal = "[" + ", ".join(
            f"(({x} : State), ({y} : State))" for x, y in result["pairs"]
        ) + "]"
        lines.extend([
            "def safe (u v : State) : Bool :=",
            f"  decide ((u, v) ∈ ({literal} : List (State × State)))",
            "theorem safe_origin : safe originLeft originRight = true := by decide",
            "theorem safe_step :",
            "    ∀ (u v : State) (a : Action), safe u v = true →",
            "      safe (step a u) (step a v) = true := by decide",
            "theorem safe_readout :",
            "    ∀ (u v : State), safe u v = true → readout u = readout v := by decide",
            "",
            "theorem safe_run (w : List Action) :",
            "    ∀ u v : State, safe u v = true →",
            "      safe (run w u) (run w v) = true := by",
            "  induction w with",
            "  | nil =>",
            "      intro u v h",
            "      exact h",
            "  | cons a tail ih =>",
            "      intro u v h",
            "      exact ih (step a u) (step a v) (safe_step u v a h)",
            "",
            "theorem all_words_same (w : List Action) :",
            "    readout (run w originLeft) = readout (run w originRight) := by",
            "  exact safe_readout _ _ (safe_run w originLeft originRight safe_origin)",
        ])
        theorems = ["safe_origin", "safe_step", "safe_readout",
                    "safe_run", "all_words_same"]
    lines.extend(["", f"end {namespace}", ""])
    for theorem in theorems:
        lines.append(f"#print axioms {namespace}.{theorem}")
    lines.append("")
    return "\n".join(lines), [f"{namespace}.{name}" for name in theorems]


def ite_actions(rows: list[str]) -> str:
    expr = rows[-1]
    for a in reversed(range(len(rows) - 1)):
        expr = f"if a.val = {a} then ({rows[a]}) else ({expr})"
    return expr


def dump(path: Path, obj: dict) -> None:
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False,
                               sort_keys=True) + "\n", encoding="utf-8")


def generate(requests: Path, output: Path, head: str) -> int:
    if not HEAD.fullmatch(head):
        raise ValueError("head must be the complete, exact Git commit SHA")
    if not requests.is_dir():
        raise ValueError("requests directory missing")
    paths = sorted(requests.glob("*.json"))
    if not paths or len(paths) > MAX_FILES:
        raise ValueError("1..12 request files required")
    if output.exists() and any(output.iterdir()):
        raise ValueError("output directory must be empty to prevent stale evidence")
    # Validate everything before writing a partial batch.
    models = [read_request(path) for path in paths]
    results = [solve(model) for model in models]
    for model, result in zip(models, results):
        validate_result(model, result)
    output.mkdir(parents=True, exist_ok=True)
    records = []
    for path, model, result in zip(paths, models, results):
        source, theorems = lean_source(model, result)
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", source):
            raise ValueError("generated source contains forbidden proof shortcut")
        (output / (model["name"] + ".lean")).write_text(source, encoding="utf-8")
        record = {
            "model": model["name"], "source_request": path.as_posix(),
            "request_sha256": sha256(path.read_bytes()).hexdigest(),
            "generated_lean_sha256": sha256(source.encode("utf-8")).hexdigest(),
            "checkout_sha": head, "python_result": result,
            "theorems": theorems, "status": "PENDING_KERNEL_VERIFICATION",
            "kernel_verified": False,
        }
        dump(output / (model["name"] + ".json"), record)
        records.append(model["name"])
    dump(output / "manifest.json", {"schema_version": 1, "checkout_sha": head,
                                    "models": records, "passed": False})
    print(json.dumps({"models": records, "python_candidates": len(records),
                      "kernel_verified": False}))
    return 0


def audit(output: Path) -> int:
    manifest = json.loads((output / "manifest.json").read_text(encoding="utf-8"))
    all_ok = True
    for name in manifest["models"]:
        path = output / (name + ".json")
        record = json.loads(path.read_text(encoding="utf-8"))
        src = (output / (name + ".lean")).read_bytes()
        ok = sha256(src).hexdigest() == record["generated_lean_sha256"]
        logpath = output / (name + ".log")
        exitpath = output / (name + ".exit")
        if not logpath.is_file() or not exitpath.is_file():
            ok = False
            log = ""
        else:
            log = logpath.read_text(encoding="utf-8", errors="replace")
            ok &= exitpath.read_text(encoding="utf-8").strip() == "0"
        ok &= not re.search(r"(error:|warning:|sorryAx)", log)
        no_axioms = log.count("does not depend on any axioms")
        used = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
        ok &= no_axioms + len(used) == len(record["theorems"])
        for entry in used:
            axioms = {part.strip() for part in entry.split(",") if part.strip()}
            ok &= axioms <= ALLOWED_AXIOMS
        record["status"] = "LEAN_VERIFIED" if ok else "KERNEL_CHECK_FAILED"
        record["kernel_verified"] = bool(ok)
        record["axiom_audit"] = {
            "theorems_expected": len(record["theorems"]),
            "no_axiom_results": no_axioms,
            "allowed_axiom_results": len(used),
            "passed": bool(ok),
        }
        dump(path, record)
        all_ok &= bool(ok)
    manifest["passed"] = bool(all_ok)
    dump(output / "manifest.json", manifest)
    print(json.dumps({"passed": bool(all_ok), "models": manifest["models"]}))
    return 0 if all_ok else 1


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    gen = sub.add_parser("generate")
    gen.add_argument("--requests", type=Path, required=True)
    gen.add_argument("--output", type=Path, required=True)
    gen.add_argument("--head", required=True)
    check = sub.add_parser("audit")
    check.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    if args.command == "generate":
        return generate(args.requests, args.output, args.head)
    return audit(args.output)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"PROOF_FORGE_ERROR: {exc}", file=sys.stderr)
        sys.exit(2)
