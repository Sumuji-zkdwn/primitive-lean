"""Check additive proof sources against the unchanged joint assembly.

Run linear_input/verify_lean.py first, or use tools/verify.py for both stages.
MainResult.lean prepends the additive Mathlib imports listed in EXTRA_IMPORTS, then the
byte-exact verified All.lean, the registered supplements and the all-declaration axiom audit.
The original All.lean bytes are preserved without modification.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
OUT = ROOT / "verification"
PROOFS = ROOT / "linear_input/lean_check"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# Additive Mathlib imports prepended to MainResult.lean (All.lean bytes stay unchanged).
EXTRA_IMPORTS = (
    "Mathlib.Data.Nat.Squarefree",
    "Mathlib.FieldTheory.RatFunc.IntermediateField",
    "Mathlib.Data.Nat.Factorization.Defs",
    "Mathlib.RingTheory.UniqueFactorizationDomain.Basic",
    "Mathlib.Data.PNat.Factors",
)

SUPPLEMENTS = (
    ('linear_input/lean_check/MainResult.inc', 'LinearInputMainResult'),
    ('linear_input/lean_check/GeneralMinimum.inc', 'LinearInputMinimum'),
    ('linear_input/lean_check/SupportComposition.inc', 'LinearInputSupportComposition'),
    ('linear_input/lean_check/QuarticClassification.inc', 'LinearInputQuarticClassification'),
    ('linear_input/lean_check/CurvatureRigidity.inc', 'LinearInputCurvatureRigidity'),
    ('linear_input/lean_check/HistorySignature.inc', 'LinearInputHistorySignature'),
    ('linear_input/lean_check/BranchForgetting.inc', 'LinearInputBranchForgetting'),
    ('linear_input/lean_check/VariablePairObservations.inc', 'LinearInputVariablePairs'),
    ('linear_input/lean_check/BranchFibers.inc', 'LinearInputBranchFibers'),
    ('linear_input/lean_check/F0Retractions.inc', 'LinearInputF0'),
    ('linear_input/lean_check/F0Counting.inc', 'LinearInputF0Counting'),
    ('linear_input/lean_check/F0MergeChains.inc', 'LinearInputF0Merge'),
    ('linear_input/lean_check/FiniteBayes.inc', 'LinearInputBayes'),
    ('linear_input/lean_check/FourBayes.inc', 'LinearInputFourBayes'),
    ('linear_input/lean_check/GaloisChebyshev.inc', 'LinearInputGaloisChebyshev'),
    ('linear_input/lean_check/KummerDihedral.inc', 'LinearInputKummerDihedral'),
    ('linear_input/lean_check/VariablePairGaloisBridge.inc', 'LinearInputVariablePairGalois'),
    ('linear_input/lean_check/F16Holonomy.inc', 'LinearInputF16Holonomy'),
    ('linear_input/lean_check/F16RecoverySpectrum.inc', 'LinearInputF16Recovery'),
    ('linear_input/lean_check/F16RankCertificate.inc', 'LinearInputF16Rank'),
    ('linear_input/lean_check/F16RealDeterminant.inc', 'LinearInputF16Determinant'),
    ('linear_input/lean_check/F16CompleteRank.inc', 'LinearInputF16CompleteRank'),
    ('linear_input/lean_check/F16UnexpectedBridges.inc', 'LinearInputF16UnexpectedBridges'),
    ('linear_input/lean_check/ShearCommutator.inc', 'LinearInputShearCommutator'),
    ('linear_input/lean_check/ComplementaryPencilRecovery.inc', 'LinearInputComplementaryPencilRecovery'),
    ('linear_input/lean_check/F16ConstructiveRecovery.inc', 'LinearInputF16ConstructiveRecovery'),
    ('linear_input/lean_check/ComplementaryObservationExamples.inc', 'LinearInputComplementaryObservationExamples'),
    ('linear_input/lean_check/StrangeOperatorGalois.inc', 'LinearInputStrangeGalois'),
    ('linear_input/lean_check/StrangeOperatorConjugacy.inc', 'LinearInputStrangeConjugacy'),
    ('linear_input/lean_check/StrangeOperatorBoundary.inc', 'LinearInputStrangeBoundary'),
    ('linear_input/lean_check/StrangeOperatorFixedSets.inc', 'LinearInputStrangeFixedSets'),
    ('linear_input/lean_check/StrangeOperatorCounting.inc', 'LinearInputStrangeCounting'),
    ('linear_input/lean_check/F16SaddleCantor.inc', 'LinearInputF16SaddleCantor'),
    ('linear_input/lean_check/F16FullMatrix.inc', 'LinearInputF16FullMatrix'),
    ('linear_input/lean_check/F16FullRank.inc', 'LinearInputF16FullRank'),
    ('linear_input/lean_check/F0UpdateDescent.inc', 'LinearInputF0Descent'),
    ('linear_input/lean_check/Rule481Symmetry.inc', 'LinearInputRule481'),
    ('linear_input/lean_check/HannaJetCorrection.inc', 'LinearInputHannaJets'),
    ('linear_input/lean_check/FutureObservations.inc', 'LinearInputFutureObservation'),
    ('linear_input/lean_check/FutureFiniteHorizon.inc', 'LinearInputFutureHorizon'),
    ('linear_input/lean_check/OperatorWordObservations.inc', 'LinearInputOperatorWords'),
    ('linear_input/lean_check/MonoEyeComposition.inc', 'LinearInputMonoEyeComposition'),
    ('linear_input/lean_check/OperatorBisimulation.inc', 'LinearInputOperatorBisimulation'),
    ('linear_input/lean_check/OperatorVocabularyRefinement.inc', 'LinearInputOperatorRefinement'),
    ('linear_input/lean_check/OperatorFiniteHorizon.inc', 'LinearInputOperatorHorizon'),
    ('linear_input/lean_check/OperatorSemanticClosure.inc', 'LinearInputOperatorSemanticClosure'),
    ('linear_input/lean_check/CrossSystemObservation.inc', 'LinearInputCrossSystemObservation'),
    ('linear_input/lean_check/SemanticIntervalNecessity.inc', 'LinearInputSemanticIntervals'),
    ('linear_input/lean_check/FiniteSelfSynthesis.inc', 'LinearInputFiniteSelfSynthesis'),
    ('linear_input/lean_check/RecursiveOperatorReentry.inc', 'LinearInputRecursiveReentry'),
    ('linear_input/lean_check/RuleSelfModification.inc', 'LinearInputRuleSelfModification'),
    ('linear_input/lean_check/MetaRuleSelfExtension.inc', 'LinearInputMetaRuleExtension'),
    ('linear_input/lean_check/HigherOrderLiftSelfRewriting.inc', 'LinearInputHigherOrderLiftSelfRewriting'),
    ('linear_input/lean_check/EWFSFenchel.inc', 'LinearInputEWFSDual'),
    ('linear_input/lean_check/WFSCanonicalLift.inc', 'LinearInputWFSCanonical'),
    ('linear_input/lean_check/EWFSFutureBridge.inc', 'LinearInputEWFSFuture'),
    ('linear_input/lean_check/TemporalSampling.inc', 'LinearInputTemporalSampling'),
    ('linear_input/lean_check/WFSMobiusFourier.inc', 'LinearInputWFSMobiusFourier'),
    ('linear_input/lean_check/EnergyWfsFenchel.inc', 'LinearInputEnergyGaugeFenchel'),
    ('linear_input/lean_check/ObservationRetractionPolarity.inc', 'LinearInputObservationRetractionPolarity'),
    ('linear_input/lean_check/F0FutureMinimality.inc', 'LinearInputF0FutureMinimality'),
    ('linear_input/lean_check/WFSProjectiveSampling.inc', 'LinearInputWFSObservation'),
    ('linear_input/lean_check/RepresentationBridges.inc', 'LinearInputRepresentationBridges'),
    ('linear_input/lean_check/HistoryNonpreservation.inc', 'LinearInputHistoryNonpreservation'),
    ('linear_input/lean_check/TemporalLocalExtinction.inc', 'LinearInputTemporalExtinction'),
    ('linear_input/lean_check/LocalCapacityIncompatibility.inc', 'LinearInputCapacityExtinction'),
    ('linear_input/lean_check/CooperativeGluingObstruction.inc', 'LinearInputCooperativeGluing'),
    ('linear_input/lean_check/RelationalOddCycleGluing.inc', 'LinearInputRelationalGluing'),
    ('linear_input/lean_check/JoinContextualEquivalence.inc', 'LinearInputJoinContexts'),
    ('linear_input/lean_check/CurveLetterContextualEquivalence.inc', 'LinearInputCurveLetters'),
    ('linear_input/lean_check/RadicalF0Bridge.inc', 'LinearInputRadicalF0'),
    ('linear_input/lean_check/PilotComparisonBridge.inc', 'LinearInputPilotComparison'),
    ('linear_input/lean_check/PilotVolumeTransport.inc', 'LinearInputPilotTransport'),
    ('linear_input/lean_check/PilotHullInflation.inc', 'LinearInputPilotHullInflation'),
    ('linear_input/lean_check/PilotHullStability.inc', 'LinearInputPilotHullStability'),
    ('linear_input/lean_check/ElasticaOperatorBridge.inc', 'LinearInputElasticaOperatorBridge'),
    ('linear_input/lean_check/ObservableRigidPoint.inc', 'LinearInputRigidPoint'),
    ('linear_input/lean_check/ChebyshevDihedralDescent.inc', 'LinearInputChebyshevDescent'),
    ('linear_input/lean_check/ChebyshevRatFuncDegrees.inc', 'LinearInputChebyshevNext'),
    ('linear_input/lean_check/ChebyshevDegreeTower.inc', 'LinearInputChebyshevTower'),
    ('linear_input/lean_check/ChebyshevSplittingField.inc', 'LinearInputChebyshevSplitting'),
    ('linear_input/lean_check/ChebyshevGaloisAutomorphisms.inc', 'LinearInputChebyshevAutomorphisms'),
    ('linear_input/lean_check/RimObservability.inc', 'LinearInputRimObservability'),
    ('linear_input/lean_check/ViscousRewrite.inc', 'LinearInputViscousRewrite'),
    ('linear_input/lean_check/GravityCocycle.inc', 'LinearInputGravityCocycle'),
    ('linear_input/lean_check/GravityObserver.inc', 'LinearInputGravityObserver'),
    ('linear_input/lean_check/GravityObservation.inc', 'LinearInputGravityObservation'),
    ('linear_input/lean_check/TernaryZeroCesaro.inc', 'LinearInputTernaryZero'),
    ('linear_input/lean_check/FiniteObservationSeparation.inc', 'LinearInputFiniteObservation'),
    ('linear_input/lean_check/DecompositionIdentification.inc', 'LinearInputDecompositionIdentification'),
    ('linear_input/lean_check/DecompositionF0Bridge.inc', 'LinearInputDecompositionF0Bridge'),
    ('linear_input/lean_check/PrimeFactorIdentification.inc', 'LinearInputPrimeFactorIdentification'),
    ('linear_input/lean_check/PrimeSplitNormalForm.inc', 'LinearInputPrimeSplitNormalForm'),
    ('linear_input/lean_check/AssociatesFactorIdentification.inc', 'LinearInputAssociatesFactorIdentification'),
    ('linear_input/lean_check/GeneratedNonUniqueMonoid.inc', 'LinearInputGeneratedNonUnique'),
    ('linear_input/lean_check/HalfFactorialIdentification.inc', 'LinearInputHalfFactorial'),
    ('linear_input/lean_check/AtomicGeneratorClassification.inc', 'LinearInputAtomicGeneratorClassification'),
    ('linear_input/lean_check/AtomicHalfFactorial.inc', 'LinearInputAtomicHalfFactorial'),
    ('linear_input/lean_check/AtomicWordProbe.inc', 'LinearInputAtomicWordProbe'),
    ('linear_input/lean_check/SingleSwapFiber.inc', 'LinearInputSingleSwapFiber'),
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", "utf-8")


def canonical_path(relative):
    return (ROOT / "linear_input" / relative).resolve().relative_to(ROOT).as_posix()


def dependency_revisions(expected):
    rows = []
    for package in expected:
        proc = subprocess.run(["git", "rev-parse", "HEAD"],
            cwd=LEAN / ".lake/packages" / package["name"],
            capture_output=True, encoding="utf-8", errors="replace")
        actual = proc.stdout.strip()
        rows.append(dict(name=package["name"], expected=package["expected"], actual=actual,
                         match=proc.returncode == 0 and actual == package["expected"]))
    return rows


def main():
    OUT.mkdir(exist_ok=True)
    report = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=False,
        baseline_report="linear_input/lean_results.json",
        supplemental_source="linear_input/lean_check/MainResult.inc",
        supplemental_sources=[source for source, _ in SUPPLEMENTS],
        supplemental_groups=[],
        assembled_source="linear_input/lean_check/MainResult.lean",
        assembly="EXTRA_IMPORTS, then exact verified All.lean and each supplemental source in registered order, followed by all public axiom audits.",
        errors=[], declarations=[], theorem_count=0, declaration_count=0,
        all_declarations=[], total_theorem_count=0, total_declaration_count=0,
        axioms={}, unexpected=[], forbidden_tokens=[], warnings=[],
        source_hashes={}, changed_during_verification=[], dependencies=[],
        baseline_axioms_match=False, joint_axiom_audit=False, compile=None)
    log_path = OUT / "main-result.log"
    log_path.write_text("Supplemental verification has not yet compiled.\n", "utf-8")
    try:
        baseline_path = ROOT / report["baseline_report"]
        baseline = json.loads(baseline_path.read_text("utf-8"))
        if not baseline["passed"]:
            raise ValueError("The unchanged baseline verifier did not pass")
        if baseline["compile"]["exit_code"] != 0 or baseline["parent_library_build"]["exit_code"] != 0:
            raise ValueError("The baseline build or joint compile failed")
        original = [{**d, "file": canonical_path(d["file"])}
                    for d in baseline["parent_declarations"] + baseline["declarations"]]
        original_axioms = {**baseline["parent_axioms"], **baseline["axioms"]}
        hashes = {canonical_path(rel): digest for rel, digest in baseline["source_sha256"].items()}
        stale = [rel for rel, digest in hashes.items()
                 if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest]
        if stale:
            raise ValueError("Stale baseline source hashes: " + ", ".join(stale))
        if len(original_axioms) != len(original) or set(original_axioms) != {d["name"] for d in original}:
            raise ValueError("The baseline axiom audit is incomplete")
        if not all(package["match"] for package in baseline["dependencies"]):
            raise ValueError("The baseline dependency revisions did not pass")
        report["dependencies"] = dependency_revisions(baseline["dependencies"])
        if not all(package["match"] for package in report["dependencies"]):
            raise ValueError("A pinned dependency revision changed after the baseline check")

        spec = importlib.util.spec_from_file_location("common_verifier", ROOT / "tools/verify.py")
        common = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(common)
        supplement_bytes = []
        for source, namespace in SUPPLEMENTS:
            raw = (ROOT / source).read_bytes()
            supplement_bytes.append(raw)
            hashes[source] = hashlib.sha256(raw).hexdigest()
            code = common.strip_comments_strings(raw.decode("utf-8"))
            namespaces = re.findall(r"(?m)^namespace\s+([^\s]+)", code)
            if namespaces != [namespace]:
                raise ValueError(source + " must use the sole namespace " + namespace)
            if re.search(r"(?m)^\s*import\b", code):
                raise ValueError(source + " must use the imports already present in All.lean")
            for found in re.finditer(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code):
                report["forbidden_tokens"].append(dict(file=source,
                    token=found.group(), line=code.count("\n", 0, found.start()) + 1))
            declarations = []
            for found in re.finditer(
                    r"(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)",
                    code):
                declarations.append(dict(name=namespace + "." + found.group(2),
                    kind=found.group(1), file=source,
                    line=code.count("\n", 0, found.start()) + 1))
            if not declarations:
                raise ValueError("No supplemental public declarations found in " + source)
            report["supplemental_groups"].append(dict(
                source=source, namespace=namespace, declarations=declarations,
                theorem_count=sum(d["kind"] in ("theorem", "lemma") for d in declarations),
                declaration_count=len(declarations), sha256=hashes[source]))
            report["declarations"].extend(declarations)
        all_declarations = original + report["declarations"]
        if len({d["name"] for d in all_declarations}) != len(all_declarations):
            raise ValueError("Duplicate declaration names in the combined audit")
        report.update(theorem_count=sum(d["kind"] in ("theorem", "lemma") for d in report["declarations"]),
            declaration_count=len(report["declarations"]), all_declarations=all_declarations,
            total_theorem_count=sum(d["kind"] in ("theorem", "lemma") for d in all_declarations),
            total_declaration_count=len(all_declarations),
            baseline_theorem_count=baseline["theorem_count"] + baseline["parent_theorem_count"],
            baseline_declaration_count=len(original), version=baseline["version"])
        if report["forbidden_tokens"]:
            raise ValueError("Forbidden proof tokens in the supplemental source")

        # Preserve every input byte for byte, including its original newlines.
        assembled = ("".join(f"import {m}\n" for m in EXTRA_IMPORTS).encode("utf-8") +
            b"\n".join([(PROOFS / "All.lean").read_bytes(), *supplement_bytes])
            + b"\n\n-- Audit the additive proof declarations.\n"
            + ("\n".join("#print axioms " + d["name"] for d in report["declarations"]) + "\n").encode("utf-8"))
        (ROOT / report["assembled_source"]).write_bytes(assembled)
        for rel in (report["baseline_report"], report["assembled_source"],
                    "tools/verify_main_result.py", "tools/verify.py", "tools/check_delivery.py"):
            hashes[rel] = sha(ROOT / rel)
        report["source_hashes"] = hashes
        started = time.monotonic()
        command = ["lake", "env", "lean", "--trust=0", "../linear_input/lean_check/MainResult.lean"]
        proc = subprocess.run(command, cwd=LEAN, capture_output=True,
                              encoding="utf-8", errors="replace")
        log = proc.stdout + proc.stderr
        log_path.write_text(log, "utf-8")
        report["compile"] = dict(command=command, working_directory=str(LEAN), exit_code=proc.returncode,
            seconds=round(time.monotonic() - started, 3), log="verification/main-result.log")
        report["warnings"] = [line for line in log.splitlines() if re.search(r"\bwarning:", line)]
        for declaration in all_declarations:
            name = declaration["name"]
            matches = re.findall("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", log, re.S)
            no_axioms = log.count("'" + name + "' does not depend on any axioms")
            if len(matches) + no_axioms != 1:
                report["unexpected"].append(name + ": missing or duplicate audit result")
                continue
            axioms = [item.strip() for item in matches[0].split(",") if item.strip()] if matches else []
            report["axioms"][name] = axioms
            report["unexpected"].extend(name + ": " + ax for ax in axioms if ax not in ALLOWED)
        report["baseline_axioms_match"] = all(report["axioms"].get(name) == axioms
                                              for name, axioms in original_axioms.items())
        report["joint_axiom_audit"] = len(report["axioms"]) == len(all_declarations)
        report["changed_during_verification"] = [rel for rel, digest in hashes.items()
            if not (ROOT / rel).is_file() or sha(ROOT / rel) != digest]
        after_dependencies = dependency_revisions(baseline["dependencies"])
        report["dependencies_after_compile"] = after_dependencies
        if proc.returncode != 0:
            report["errors"].append("Supplemental joint compilation failed")
        if report["warnings"]:
            report["errors"].append("Lean emitted warnings")
        if report["unexpected"] or not report["joint_axiom_audit"] or not report["baseline_axioms_match"]:
            report["errors"].append("Supplemental joint axiom audit failed")
        if report["changed_during_verification"]:
            report["errors"].append("Verified inputs changed during compilation")
        if not all(package["match"] for package in after_dependencies):
            report["errors"].append("A dependency revision changed during compilation")
        report["passed"] = not report["errors"]
    except (OSError, ValueError, KeyError, TypeError) as error:
        report["errors"].append(str(error))
    report["log_sha256"] = sha(log_path)
    report["scope"] = ("The original checker and its 60 proof sources remain unchanged. "
        "This second --trust=0 compilation audits the original declarations, the additive main result "
        "and the general fixed-input minimum, support composition, quartic classification and curvature rigidity criteria "
        "in one assembled Lean session. It verifies proofs, not numerical simulations or browser rendering.")
    write_json(OUT / "main-result.json", report)
    print(json.dumps({key: report[key] for key in ("passed", "theorem_count", "declaration_count",
        "total_theorem_count", "total_declaration_count", "compile", "errors", "unexpected",
        "warnings", "forbidden_tokens", "changed_during_verification")}, ensure_ascii=False, indent=2))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
