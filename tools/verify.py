"""Verify retained proof groups and additive compositions through one entry point.

Usage: python -X utf8 tools/verify.py [--rebuild] [--lean-only | --proof-only]
--rebuild removes only lean/.lake/build; pinned dependency caches are retained.
--proof-only checks fresh proofs without requiring the separate historical archive audit.
--lean-only runs the unchanged joint checker, then audits all registered
supplements together with all original declarations.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, shutil, subprocess, sys, time, zipfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
OUT = ROOT / "verification"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def strip_comments_strings(source):
    """Keep source line offsets while excluding nested comments and strings."""
    result=[]; i=0; depth=0; string=False
    while i<len(source):
        c=source[i]; pair=source[i:i+2]
        if depth:
            if pair=='/-':depth+=1;result.extend('  ');i+=2;continue
            if pair=='-/':depth-=1;result.extend('  ');i+=2;continue
            result.append('\n' if c=='\n' else ' ');i+=1;continue
        if string:
            if c=='\\':result.extend('  ');i+=2;continue
            if c=='"':string=False
            result.append('\n' if c=='\n' else ' ');i+=1;continue
        if pair=='/-':depth=1;result.extend('  ');i+=2;continue
        if pair=='--':
            end=source.find('\n',i);end=len(source) if end<0 else end
            result.extend(' '*(end-i));i=end;continue
        if c=='"':string=True;result.append(' ');i+=1;continue
        result.append(c);i+=1
    return ''.join(result)

def command(args, name, cwd=ROOT):
    started=time.monotonic()
    proc=subprocess.run(args,cwd=cwd,text=True,encoding="utf-8",errors="replace",capture_output=True)
    output=proc.stdout+proc.stderr
    (OUT/(name+".log")).write_text(output,encoding="utf-8")
    warnings=[line for line in output.splitlines() if re.search(r"\bwarning:",line)]
    return dict(command=args,working_directory=str(cwd),exit_code=proc.returncode,
                seconds=round(time.monotonic()-started,3),log="verification/"+name+".log",
                warnings=warnings)

def canonical_path(relative):
    return (ROOT / "linear_input" / relative).resolve().relative_to(ROOT).as_posix()


def verify_lean(rebuild):
    if rebuild:
        target = (LEAN / ".lake/build").resolve()
        if target != LEAN.resolve() / ".lake/build":
            raise RuntimeError("Unsafe project build path")
        if target.exists():
            shutil.rmtree(target)
    # The proof files and their existing checker retain their separate roles.
    run = command([sys.executable, "-X", "utf8", "linear_input/verify_lean.py"], "joint-lean-run")
    current = json.loads((ROOT / "linear_input/lean_results.json").read_text("utf-8"))
    original_declarations = [{**d, "file": canonical_path(d["file"])}
                    for d in current["parent_declarations"] + current["declarations"]]
    before = json.loads((OUT / "before-unification.json").read_text("utf-8"))
    archive_path = ROOT / before["archive"]
    assert sha(archive_path) == before["archive_sha256"]
    with zipfile.ZipFile(archive_path) as archive:
        old = json.loads(archive.read("linear_input/lean_results.json"))
        old_names = {d["name"]: d["kind"] for d in old["parent_declarations"] + old["declarations"]}
        new_names = {d["name"]: d["kind"] for d in original_declarations}
        proof_files = sorted(set(d["file"] for d in original_declarations))
        unchanged = [rel for rel in proof_files if (ROOT / rel).read_bytes() == archive.read(rel)]
    preservation = dict(passed=len(unchanged) == len(proof_files) and old_names == new_names,
        proof_files=len(proof_files), byte_identical_proof_files=len(unchanged),
        same_public_names_and_kinds=old_names == new_names,
        missing=sorted(old_names.keys() - new_names.keys()), added=sorted(new_names.keys() - old_names.keys()),
        archive=before["archive"])
    warnings = []
    for rel in (current["compile"]["log"], current["parent_library_build"]["log"]):
        warnings += [line for line in (ROOT / "linear_input" / rel).read_text("utf-8").splitlines()
                     if re.search(r"\bwarning:", line)]
    supplement_run = command([sys.executable, "-X", "utf8", "tools/verify_main_result.py"], "main-result-run")
    supplement_path = OUT / "main-result.json"
    supplement = json.loads(supplement_path.read_text("utf-8"))
    declarations = original_declarations + supplement["declarations"]
    axioms = supplement["axioms"]
    hashes = {canonical_path(rel): digest for rel, digest in current["source_sha256"].items()}
    hashes.update(supplement["source_hashes"])
    hashes["tools/verify.py"] = sha(Path(__file__))
    hashes["verification/main-result.json"] = sha(supplement_path)
    warnings += supplement["warnings"]
    changed = [rel for rel, digest in hashes.items() if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest]
    passed = (run["exit_code"] == 0 and current["passed"] and preservation["passed"]
              and supplement_run["exit_code"] == 0 and supplement["passed"]
              and supplement["all_declarations"] == declarations
              and len(axioms) == len(declarations) and not warnings and not changed)
    supplemental_scopes = {
        'MainResult': 'Additive connection and worked example',
        'GeneralMinimum': 'General fixed-input minimum and strict-support criteria, with quartic bridges',
        'SupportComposition': 'Support interpolation, ordering, derivative identification and shared-minimizer restrictions',
        'QuarticClassification': 'Exact quartic minimum uniqueness and supporting-input classification',
        'CurvatureRigidity': 'Conserved phase energy and the transverse square force constant curvature at a phase minimum',
        'HistorySignature': 'Actual primitive coordinates, second iterated integrals, area composition and explicit observation hierarchy',
        'BranchForgetting': 'Chebyshev normalization of the actual stationary input and an explicit minimum-only forgetting criterion',
        'VariablePairObservations': 'Actual partial derivatives, explicit inverses, sign changes and transport of observation hierarchies in the primitive energy family',
        'BranchFibers': 'Cosine candidate equality, explicit critical fibers and retractions, and exhaustive counts of the real inverse images of the ternary iterate',
        'F0Retractions': 'Idempotent retractions, K-S-C composition, compatible-map counting by an explicit equivalence, finite orbit bounds, and bridges to the critical branch representatives',
        'F0Counting': 'Actual labelled idempotent maps counted by fixed-point rank, with exact seven- and eight-point totals',
        'F0MergeChains': 'Positive integer-partition merge chains and an explicit Fin 5 fiber-mass chain realized by sequential idempotent K-S-C steps, with mass preservation, strict rank decrease, acyclicity and exact-length paths to the singleton',
        'FiniteBayes': 'Finite normalization and posterior composition, support constraints, log-loss comparison, observation pushforwards, and actual Elastica exponential-weight bridges',
        'FourBayes': 'Exploration mixtures, calibrated disappointment, binary log-partition derivatives, cancellation of opposite tilts, and exact deletion and predictive-forgetting counterexamples',
        'GaloisChebyshev': 'Elementary Joukowski/Chebyshev collision identity, cyclotomic and Kummer root labels, modular reflections and existing critical-fiber kernels (not a full Galois group identification)',
        'KummerDihedral': 'Actual splitting and adjoining-root fields, cyclic Kummer Galois group equivalence, Galois degree, and dihedral group action on root labels (not yet a dihedral field-Galois identification)',
        'VariablePairGaloisBridge': 'Actual variable-pair stationary reduction to a cubic, Hessian-discriminant degeneracies, Chebyshev normalization, and the eight sign classes under coordinate reflections',
        'F16Holonomy': 'Finite Cayley-Dickson epsilon table, 128 signed observation squares, F0 idempotent forgetting and right-probe descent classification',
        'F16RecoverySpectrum': 'Constructive recovery of the forgotten bit by an obstructed probe, explicit signed 2x2 pencil factors, and four null vectors at each singular input',
        'F16RankCertificate': 'Exact integer factor and 12-by-12 pivot certificates imply real Matrix.rank 12 at t = +1 and -1',
        'F16RealDeterminant': 'Eight 2-by-2 sedenion left-pencil blocks, verified row/column bijections and parity, and the full real Matrix.det identity',
        'F16CompleteRank': 'Exact real-pencil comparison at integer parameters, determinant-zero characterization, and complete rank-12/rank-16 classification',
        'F16UnexpectedBridges': 'Exact signed F16 block normal forms, D4 reflection-rotation relations, cubic discriminant degeneracy, and two singular probes jointly identifying the full state',
        'ShearCommutator': 'Actual energy partial derivatives generate horizontal and vertical shears through coordinate exchange; inverse-order cancellation, unit-determinant hyperbolic commutator, and a certified exponential lower bound',
        'ComplementaryPencilRecovery': 'Constructive inverse for opposite matrix-pencil observations, compatible-data equivalence, uniqueness, and exact kernel criteria',
        'F16ConstructiveRecovery': 'General inverse theorem instantiated with the original rank-12 F16 real matrices and exact reconstruction of both observations',
        'ComplementaryObservationExamples': 'Counterexamples at missing assumptions and an independent PR19 four-phase coordinate observation model',
        'StrangeOperatorGalois': 'F0-derived self-stopping, fiber obstruction and relational Galois closure',
        'StrangeOperatorConjugacy': 'Naturality, one-point F0 closure classification and conjugacy orbit',
        'StrangeOperatorBoundary': 'Finite non-idempotent obstruction to extending the spike-orbit theorem to arbitrary F0 maps',
        'StrangeOperatorFixedSets': 'Complete singleton Galois closure classification by fixed-point sets',
        'F16SaddleCantor': 'F16 reflection-derived hyperbolic saddle, finite two-branch ternary coding and the F0 two-cycle obstruction; no infinite fractal/dimension theorem.',
        'F16FullMatrix': 'Actual real 16-by-16 sedenion left-pencil matrix, explicit eight-block row/column permutation equivalence, full determinant and real singularity classification',
        'F16FullRank': 'Invertible 2-by-2 Gaussian elimination, global diagonalization and rank 12 exactly at t=±1 (rank 16 otherwise)',
        'F0UpdateDescent': 'Induced dynamics on F0 fixed representatives, descent iff fiber respect, composition, symmetry preservation and a finite counterexample',
        'Rule481Symmetry': 'Local Rule 481 reflection/complement and finite 3x3 torus mirror equivariance and two-cycle (not infinite-lattice OEIS coefficient proof)',
        'HannaJetCorrection': 'First-jet formal-series calculation: the k=3 denominator correction changes the local x^7 coefficient by eight (not the whole generating function)',
        'FutureObservations': 'Future observation equivalence, induced deterministic quotient state, universal minimal predictive kernel, and observation-invisible symmetries',
        'FutureFiniteHorizon': 'Finite observation signatures, monotone trace rank, and stabilization after at most N-r refinement steps',
        'OperatorWordObservations': 'Operator-word observational equivalence, canonical quotient states, compilation without new distinctions, and an independent-action counterexample',
        'OperatorBisimulation': 'Greatest observational bisimulation, closure operations, representation fibers and invisible symmetries',
        'OperatorVocabularyRefinement': 'Conservative extension criterion, strict new-action witnesses, quotient surjection and quotient splits',
        'OperatorFiniteHorizon': 'Finite-state multi-action trace profiles, plateau test, N-r bound and short separating words',
        'OperatorSemanticClosure': 'Semantically compatible operators, induced quotient endomorphisms, functoriality, and a conservative nonword-generatable finite witness',
        'SemanticIntervalNecessity': 'Finite prefix-time survival of local systems, old invariant extinction barrier, fresh-operation necessity, finite strict-quotient example and one-local extinction counterexample',
        'FiniteSelfSynthesis': 'Executable finite local repair search, complete bounded-catalog oracle, nonword-generable interval restoration, and Fin 3 instantiated repair/refinement',
        'RecursiveOperatorReentry': 'Finite child-generated novel operator catalogue, fresh patch construction, sound and complete bounded frontier, reentry monotonicity, conditional local viability, three-round saturation example',
        'RuleSelfModification': 'Mutable internal rule-edge table, bounded generation meta-compiler, reactivation requiring an actual rule edit, finite startup and saturation, conditional interval survival bridge',
        'MetaRuleSelfExtension': 'Mutable second-order meta-rule catalogue, fixed higher-order lift, soundness and preservation, controlled divergent future object-level rules with identical lower-level state, finite saturation and interval viability bridge',
        'HigherOrderLiftSelfRewriting': 'State-resident lift program updated by learned operators, exact lower-level trace reproduction, finite observation classes and saturation',
        'EWFSFenchel': 'Verified reversible E polynomial, x-only forgetting obstruction, positive-intensity WFS gauge and physical-versus-changed Fenchel pairing',
        'WFSCanonicalLift': 'Positive-intensity WFS p=2 cotangent lift and p=0 momentum identity under explicit domain conditions',
        'EWFSFutureBridge': 'Coordinate-conjugate future equivalence, E x-trace full-state reconstruction, WFS2 exp observation invariance and radial rotation quotient',
        'TemporalSampling': 'General observation schedules, exact stride-sampling iff one-step congruence, phase reconstruction, and E-rotation even-time aliasing with positive WFS gauge',
        'WFSMobiusFourier': 'WFS p=2 positive-intensity Möbius involution induced by two E rotation steps and exact four-phase first Fourier coefficient with even-sample aliasing',
        'EnergyWfsFenchel': 'Exact E-gradient/Fenchel pairing transport, p=0/p=2 WFS gauges, all-u probe obstruction for F0 retractions and double-well minorants',
        'ObservationRetractionPolarity': 'Exact decode/re-observe retraction on data, compatible fixed points, Stops semantics, and singleton closure with explicit properness hypotheses.',
        'F0FutureMinimality': 'F0 descent iff the current observation kernel equals complete future equivalence, plus the concrete one-step counterexample.',
        'WFSProjectiveSampling': 'Projective conjugacy, gcd sampling kernel and cyclic phase pseudometric; adapted original PR21 with repaired proof and unchanged assumptions.',
        'RepresentationBridges': 'Exact identities of retained F16 matrix representations and energy maps, with transfer of actual complementary reconstruction.',
        'RadicalF0Bridge': 'Arithmetic radical as multiplicity-forgetting F0, exact prime-support kernel, squarefree fixed points, and successor failure of descent and predictive sufficiency',
    }
    supplemental_groups = {
        Path(group["source"]).stem: dict(
            theorem_count=group["theorem_count"], declaration_count=group["declaration_count"],
            path=group["source"], scope=supplemental_scopes[Path(group["source"]).stem])
        for group in supplement["supplemental_groups"]
    }
    result = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=passed,
        proof_layout="Existing Elastica and linear-input proofs retained; registered additions and theorem compositions audited together",
        entry_point="tools/verify.py", detailed_joint_report="linear_input/lean_results.json",
        supplemental_report="verification/main-result.json", supplemental_run=supplement_run,
        version=current["version"], clean_project_build=rebuild, dependency_cache_retained=True,
        run=run, build=current["parent_library_build"], baseline_audit=current["compile"], audit=supplement["compile"],
        declarations=declarations, theorem_count=current["theorem_count"] + current["parent_theorem_count"] + supplement["theorem_count"],
        declaration_count=len(declarations), axioms=axioms, joint_axiom_audit=supplement["joint_axiom_audit"],
        proof_groups=dict(Elastica=dict(theorem_count=current["parent_theorem_count"],
            declaration_count=current["parent_declaration_count"], path="lean/Elastica"),
            LinearInput=dict(theorem_count=current["theorem_count"], declaration_count=current["declaration_count"],
            path="linear_input/lean_check", scope="Unchanged original 36 proof parts"),
            **supplemental_groups),
        added_declarations=supplement["declarations"],
        dependencies=current["dependencies"], source_hashes=hashes,
        unexpected=current["unexpected"] + supplement["unexpected"] + supplement["errors"],
        forbidden_tokens=current["forbidden_tokens"] + supplement["forbidden_tokens"],
        warnings=warnings, changed_during_verification=changed,
        pre_unification_preservation=preservation,
        scope="The unchanged linear-input verifier builds Elastica, generates All.lean from the original 36 parts and audits the original 509 declarations. The additive checker then compiles the exact All.lean followed by every registered supplement with --trust=0 and audits all original and additional public declarations in one session. Supplements retain separate source groups and counts. Original proof files, names and configuration are preserved.",
        not_covered=[
            ("existence for arbitrary prescribed boundary/area data and regularity of weak "
             "area-constrained minimizers; the explicit circle comparison minimum is covered")
            if item == "existence and regularity of area-constrained minimizing curves" else item
            for item in current["not_covered"]])
    write_json(OUT / "lean.json", result)
    # Keep familiar top-level log links, copying actual outputs rather than relabelling old runs.
    shutil.copyfile(ROOT / "linear_input" / current["parent_library_build"]["log"], OUT / "lean-build.log")
    shutil.copyfile(OUT / "main-result.log", OUT / "lean-axioms.log")
    if rebuild and passed:
        shutil.copyfile(OUT / "lean-build.log", OUT / "clean-rebuild.log")
        write_json(OUT / "clean-rebuild.json", dict(timestamp_utc=result["timestamp_utc"],
            clean_project_build=True, dependency_cache_retained=True,
            build=current["parent_library_build"], cleaned_by="tools/verify.py --rebuild before the joint checker",
            build_log="verification/clean-rebuild.log", build_log_sha256=sha(OUT / "clean-rebuild.log"),
            source_hashes=hashes, dependencies=current["dependencies"]))
    return result


def refresh_manifest():
    files = {}
    for path in sorted(ROOT.rglob("*")):
        rel = path.relative_to(ROOT)
        if not path.is_file() or ".lake" in rel.parts or "__pycache__" in rel.parts or path.name == "manifest.json":
            continue
        files[rel.as_posix()] = sha(path)
    write_json(ROOT / "manifest.json", dict(algorithm="SHA256", files=files))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--lean-only", action="store_true")
    modes.add_argument("--proof-only", action="store_true")
    modes.add_argument("--arc3-only", action="store_true", help="Check experimental ARC integration; does not run Lean")
    modes.add_argument("--integration-only", action="store_true", help="Check integrated PR sources, offline tests and Lean proofs")
    args = parser.parse_args(argv)
    if args.arc3_only:
        if args.rebuild:
            parser.error("--rebuild applies to Lean, not --arc3-only")
        from arc3_integration import run_arc3
        report = run_arc3(ROOT)
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 0 if report["passed"] else 1
    OUT.mkdir(exist_ok=True)
    if args.integration_only:
        from pr_integration import run_integration
        result = run_integration(ROOT, command, args.rebuild)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result["passed"] else 1
    if args.proof_only:
        from proof_only import run_proof_only
        proof = run_proof_only(ROOT, command, args.rebuild)
        print(json.dumps(proof, ensure_ascii=False, indent=2))
        return 0 if proof["passed"] else 1
    lean = verify_lean(args.rebuild)
    summary = {k: lean[k] for k in ("passed", "proof_layout", "version", "clean_project_build",
        "theorem_count", "declaration_count", "proof_groups", "unexpected", "warnings", "forbidden_tokens")}
    if args.lean_only:
        print(json.dumps(summary, ensure_ascii=False, indent=2))
        return 0 if lean["passed"] else 1
    checks = {}
    for key, script in (("examples", "tools/check_examples.py"), ("scale_response", "tools/check_scale_response.py"),
                       ("combinations", "tools/check_combinations.py"), ("linear_input", "linear_input/verify.py"),
                       ("rendering", "tools/render.py")):
        checks[key] = command([sys.executable, "-X", "utf8", script], key.replace("_", "-") + "-run")
    write_json(OUT / "results.json", dict(passed=False, status="delivery validation pending"))
    write_json(ROOT / "manifest.json", dict(algorithm="SHA256", status="validation pending", files={}))
    delivery_run = command([sys.executable, "-X", "utf8", "tools/check_delivery.py"], "delivery-run")
    delivery = json.loads((OUT / "delivery.json").read_text("utf-8"))
    passed = lean["passed"] and all(check["exit_code"] == 0 for check in checks.values()) and delivery_run["exit_code"] == 0 and delivery["passed"]
    result = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=passed, lean_passed=lean["passed"],
        theorem_count=lean["theorem_count"], declaration_count=lean["declaration_count"],
        clean_project_build=args.rebuild, **checks, delivery_run=delivery_run, delivery=delivery,
        source_hashes=lean["source_hashes"])
    write_json(OUT / "results.json", result)
    refresh_manifest()
    print(json.dumps({**summary, "passed": passed, "checks": checks, "delivery_passed": delivery["passed"]}, ensure_ascii=False, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
