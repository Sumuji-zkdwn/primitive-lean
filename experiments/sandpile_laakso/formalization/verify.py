"""Build the integrated Lean proof, audit its axioms, and replay the finite suites.

From the experiment directory: python -B formalization/verify.py
Use --mathlib-root for another Lake checkout of the pinned mathlib revision.
The verifier uses the standard library. The older planar experiment uses NumPy.
"""
import argparse
from contextlib import nullcontext
from hashlib import sha256
from importlib.metadata import PackageNotFoundError, version
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CORE = "leanprover/lean4:v4.35.0"
MATH = "leanprover/lean4:v4.30.0-rc2"
MATH_REV = "5450b53e5ddc75d46418fabb605edbf36bd0beb6"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MODULES = {
    "SquareClock": ("SquareClock", {"square_phase_and_gate", "observed_commute", "sandpile_gate"}),
    "ObservedQuotient": ("ObservedSandpile", {"calibratedEquiv", "fibre_not_homeomorphic_to_cantor",
                                             "calibrated_PI_and_regular", "limitDistance_eq_standard"}),
    "ProductPI": ("SandpileLaakso.ProductPI", {"product_of_slice_PI"}),
    "WeightedPI": ("SubLaakso.WFS", {"ramp_test_PI_iff", "weighted_path_distance_bounds",
                                    "transfer_ball", "equal_dimensions_and_PI_order_iff"}),
    "CutObstruction": ("SubLaakso.Cut", {"occupation_upper", "upper_along_height",
                                         "not_wholeBallPI", "transformed_cut_obstruction"}),
    "HeightLaw": ("SingleSquare", {"sample_band_mass", "sample_wings"}),
    "RawGeometry": ("ObservedSandpile.Raw", {"height_control", "diameter_bound"}),
    "RawFailure": ("SubLaakso.RawFailure", {"no_PI_of_thin_band"}),
    "Main": ("SingleSquare", {"physical_gates", "same_samples", "raw_failure", "single_square_realization"}),
}
SUITES = [("planar_followup", "test_planar_followup.py", 5),
          ("formalization", "test_single_square.py", 3)]
PLANAR_INPUTS = ("gate_closures.py", "gate_closures_results.json", "local_response.py",
                 "local_response.json", "planar_sandpile.py", "planar_results.json",
                 "square_clock.py", "square_clock_results.json")
NAME = r"[\w'][\w'.]*"


def run(argv, cwd, data=None, env=None):
    """Keep tool diagnostics available to the JSON writer when a check fails."""
    proc = subprocess.run(argv, cwd=cwd, input=data, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=900, env=env)
    output = proc.stdout.decode("utf-8", errors="replace").replace("\r\n", "\n").strip()
    if proc.returncode:
        raise RuntimeError(f"{argv[0]} returned {proc.returncode}\n{output[-14000:]}")
    return output


def source_files():
    files = [HERE / f"{module}.lean" for module in MODULES]
    files.extend(ROOT / folder / name for folder, name, _ in SUITES)
    files.extend(ROOT / "planar_followup" / name for name in PLANAR_INPUTS)
    files.append(Path(__file__).resolve())
    return files


def hashes(paths):
    return {p.relative_to(ROOT).as_posix(): sha256(p.read_bytes()).hexdigest() for p in paths}


def compiler_info(command, directory, expected):
    banner = run([*command, "--version"], directory)
    if not banner.startswith(f"Lean (version {expected.split(':v')[1]},"):
        raise ValueError(f"Unexpected {expected} compiler banner: {banner}")
    return banner


def check_mathlib(root):
    lock = root / "lake-manifest.json"
    manifest = json.loads(lock.read_bytes())
    package = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    mathdir = root / manifest["packagesDir"] / package["name"]
    head = run(["git", "rev-parse", "HEAD"], mathdir)
    tracked = run(["git", "status", "--porcelain", "--untracked-files=no"], mathdir)
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    dep_toolchain = (mathdir / "lean-toolchain").read_text(encoding="utf-8").strip()
    if head != MATH_REV or package["rev"] != head or tracked:
        raise ValueError(f"mathlib mismatch: locked={package['rev']} HEAD={head} changes={tracked!r}")
    if toolchain != MATH or dep_toolchain != MATH:
        raise ValueError(f"Toolchain mismatch: project={toolchain}, mathlib={dep_toolchain}")
    return {"mathlib_git_head": head, "manifest_revision": package["rev"],
            "tracked_changes": False, "toolchain": toolchain,
            "lake_manifest_sha256": sha256(lock.read_bytes()).hexdigest(),
            "compiler": compiler_info(["lake", f"+{MATH}", "env", "lean"], root, MATH)}


def declarations(module, src):
    ns, required_names = MODULES[module]
    code = src.decode("utf-8-sig")
    spaces = re.findall(rf"^namespace\s+({NAME})", code, re.M)
    if len(spaces) != 1 or (ns is not None and ns != spaces[0]):
        raise ValueError(f"Unexpected namespace structure in {module}: {spaces}")
    ns = spaces[0]
    # Named sections do not change declaration names. Keep the explicit entry
    # points in addition to enumerating the public theorems in these modules.
    names = set(re.findall(rf"^theorem\s+({NAME})", code, re.M))
    names.update(re.findall(rf"^#print axioms\s+({NAME})", code, re.M))
    if not names:
        raise ValueError(f"Empty declaration audit in {module}")
    return sorted(f"{ns}.{name}" for name in names | required_names)


def audit_block(names):
    marker = "START_SANDPILE_AXIOM_REPORT"
    appendix = f'\n#eval IO.println "{marker}"\n' + "".join(f"#print axioms {n}\n" for n in names)
    return appendix.encode("utf-8")


def parse_axioms(names, output):
    prior, split, body = output.partition("START_SANDPILE_AXIOM_REPORT\n")
    if not split or re.search(r"warning:.*(?:uses|contains).*sorry", prior, re.I):
        raise ValueError(f"Incomplete or admitted proof: {output[-2000:]}")
    pattern = re.compile(rf"'({NAME})' (?:does not depend on any axioms|depends on axioms:"
                         r"\s*\[([^\]]*)\])")
    audit = {}
    for match in pattern.finditer(body):
        theorem, items = match.groups()
        deps = sorted(w.strip() for w in (items or "").split(",") if w.strip())
        if theorem in audit or (set(deps) - ALLOWED):
            raise ValueError(f"Unexpected axiom report for {theorem}: {deps}")
        audit[theorem] = deps
    if set(names) != set(audit) or pattern.sub("", body).strip():
        raise ValueError(f"Missing declarations or unparsed Lean output: {body[-2500:]}")
    return audit


def get_source(module, expected):
    source = (HERE / f"{module}.lean").read_bytes()
    digest = sha256(source).hexdigest()
    if digest != expected[f"formalization/{module}.lean"]:
        raise ValueError(f"{module}.lean changed before compilation")
    return source


def check_core(hashes_by_name):
    banner = compiler_info(["lean", f"+{CORE}"], ROOT, CORE)
    src = get_source("SquareClock", hashes_by_name)
    names = declarations("SquareClock", src)
    raw = run(["lean", f"+{CORE}", "--trust=0", "--stdin"], ROOT, src + audit_block(names))
    axioms = parse_axioms(names, raw)
    return {"passed": True, "compiler": banner, "toolchain": CORE, "trust_level": 0,
            "source_sha256": sha256(src).hexdigest(), "declarations": len(axioms), "axioms": axioms}


def integrated_build(mathlib_root, hashes_by_name, build_dir=None):
    # Ask Lake for its locked search path, then prepend a fresh olean directory.
    # Passing the three paths only avoids recording unrelated environment values.
    variables = ("LEAN_PATH", "LEAN_SYSROOT", "PATH")
    code = f"import json,os; print(json.dumps({{k:os.environ[k] for k in {variables!r}}}))"
    build_env = json.loads(run(["lake", f"+{MATH}", "env", sys.executable, "-c", code], mathlib_root))
    binary = Path(build_env["LEAN_SYSROOT"]) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    report, groups = {}, {}
    if build_dir is not None:
        build_dir.mkdir(exist_ok=True)
        if any(build_dir.iterdir()):
            raise ValueError("--build-dir must be empty so every local import is freshly compiled")
    with (nullcontext(str(build_dir)) if build_dir is not None else
          tempfile.TemporaryDirectory(prefix="laakso-kernel-")) as temp:
        directory = Path(temp)
        env = {**os.environ, **build_env, "LEAN_PATH": temp + os.pathsep + build_env["LEAN_PATH"]}
        for module in MODULES:
            src = get_source(module, hashes_by_name)
            names = declarations(module, src)
            path = directory / f"{module}.lean"
            path.write_bytes(src)
            compiled = path.with_suffix(".olean")
            output = run([binary, "--trust=0", f"--root={temp}", "-o", compiled, path], directory, env=env)
            if not compiled.is_file() or re.search(r"warning:.*(?:uses|contains).*sorry", output, re.I):
                raise ValueError(f"{module} was not built cleanly: {output[-1500:]}")
            report[module] = {"passed": True, "source_sha256": sha256(src).hexdigest(),
                              "trust_level": 0, "imports": re.findall(r"^import\s+(\S+)", src.decode(), re.M)}
            print(f"Compiled {module} at trust level zero", file=sys.stderr, flush=True)
            groups[module] = names
        all_names = sorted(name for names in groups.values() for name in names)
        imports = "".join(f"import {m}\n" for m in groups).encode("utf-8")
        audit_path = directory / "SandpileAxiomAudit.lean"
        audit_path.write_bytes(imports + audit_block(all_names))
        raw = run([binary, "--trust=0", f"--root={temp}", audit_path], directory, env=env)
        axioms = parse_axioms(all_names, raw)
        for module, names in groups.items():
            report[module].update(declarations=len(names), axioms={n: axioms[n] for n in names})
    return report


def run_suite(folder, name, expected_count):
    output = run([sys.executable, "-B", "-m", "unittest", "discover", "-s", folder,
                  "-p", name, "-v"], ROOT)
    tests = re.findall(r"^test_\w+ \(([^)]+)\).*?\.\.\. ok$", output, re.M)
    if (len(tests) != expected_count or len(set(tests)) != expected_count or
            not re.search(rf"^Ran {expected_count} tests? in [\d.]+s$", output, re.M) or
            output.splitlines()[-1] != "OK"):
        raise ValueError(f"Incomplete test suite {name}: {output[-3000:]}")
    return {"passed": True, "tests": tests, "count": len(tests)}


def checked(function, *args):
    try:
        return function(*args)
    except (OSError, subprocess.SubprocessError, ValueError, RuntimeError,
            PackageNotFoundError, StopIteration) as exc:
        return {"passed": False, "error": str(exc)}


def verify(mathlib_root, build_dir=None):
    paths = source_files()
    source = hashes(paths)
    core = checked(check_core, source)
    mathlib = checked(check_mathlib, mathlib_root)
    if mathlib.get("passed") is False:
        lean = {"passed": False, "error": "Mathlib dependency verification failed"}
    else:
        lean = checked(integrated_build, mathlib_root, source, build_dir)
    python = {name: checked(run_suite, folder, name, count) for folder, name, count in SUITES}
    unchanged = source == hashes(paths)
    return {"passed": unchanged and core["passed"] and lean.get("passed") is not False
            and all(r["passed"] for r in python.values()),
            "inputs_unchanged": unchanged, "source_sha256": source,
            "core": core, "mathlib": mathlib,
            "allowed_axioms": sorted(ALLOWED), "lean": lean,
            "python_version": sys.version.split()[0], "numpy_version": checked(version, "numpy"),
            "test_suites": python}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-root", type=Path, default=ROOT.parent / "mobius_430")
    parser.add_argument("--output", type=Path, default=HERE / "verification.json")
    parser.add_argument("--build-dir", type=Path, help="retain the new oleans in this empty directory")
    args = parser.parse_args()
    report = checked(verify, args.mathlib_root.resolve(), args.build_dir.resolve() if args.build_dir else None)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=args.output.parent,
                                     delete=False, newline="\n") as tmp:
        json.dump(report, tmp, ensure_ascii=False, indent=2)
        tmp.write("\n")
    os.replace(tmp.name, args.output)
    print(f"{'PASS' if report['passed'] else 'FAIL'}  {args.output}")
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
