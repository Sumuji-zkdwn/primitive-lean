#!/usr/bin/env python3
"""Check the additive projection/permission bridge via tools/verify.py.

Builds an isolated assembly from the actual checkout, preserving every proof
body. Only the upstream broad import header is narrowed. No source is rewritten.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

from verify import strip_comments_strings

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean'
OUT = ROOT / 'verification/projection-reachability'
PROOFS = ROOT / 'linear_input/lean_check'
FRAGMENTS = ['ProjectionReachability.inc', 'PermissionProjectionBridge.inc',
             'FiniteProjectionExamples.inc', 'ChairInternalGeneration.inc']
PREFIXES = ['LinearInputProjectionReachability', 'Elastica.ChairPieProjection',
            'LinearInputProjectionExamples', 'Elastica.ChairInternalGeneration']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assemble():
    OUT.mkdir(parents=True, exist_ok=True)
    parts = ['import Mathlib.Data.Finset.Card\nimport Mathlib.Data.Fintype.Card\n'
             'import Mathlib.Tactic.SplitIfs\nset_option maxRecDepth 2000\n']
    inputs = []
    for name in ['OperatorWordObservations.inc', 'OperatorVocabularyRefinement.inc',
                 'OperatorReachability.inc']:
        path = PROOFS / name
        parts.append(path.read_text())
        parts.append('end -- close the upstream anonymous noncomputable section\n')
        inputs.append(path)
    chair_path = LEAN / 'Research/ChairPieKillSpot.lean'
    chair = chair_path.read_text()
    if not chair.startswith('import Mathlib\n'):
        raise RuntimeError('Upstream import changed; review assembly before proceeding')
    parts.append(chair[len('import Mathlib\n'):])
    inputs.append(chair_path)
    names = []
    for name, prefix in zip(FRAGMENTS, PREFIXES):
        path = PROOFS / name
        src = path.read_text()
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', strip_comments_strings(src)):
            raise RuntimeError(f'Prohibited proof token: {path.relative_to(ROOT)}')
        parts.append(src)
        names.extend(prefix + '.' + n for n in re.findall(r'^theorem\s+(\w+)', src, re.M))
        inputs.append(path)
    if len(names) != 35:
        raise RuntimeError(f'Review expected theorem inventory: {len(names)} instead of 35')
    parts.append('\n'.join('#print axioms ' + n for n in names) + '\n')
    export = PROOFS / 'ChairProjectionExport.inc'
    parts.append(export.read_text())
    inputs.extend([export, ROOT / 'tools/chair_pie_killspot.py', Path(__file__),
                   ROOT / 'tools/projection_reachability_finite.py', ROOT / 'tools/verify.py',
                   LEAN / 'lean-toolchain', LEAN / 'lake-manifest.json'])
    assembly = OUT / 'ProjectionCheck.lean'
    assembly.write_text('\n'.join(parts))
    hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in inputs}
    metadata = dict(theorem_names=names, public_theorems=len(names),
                    assembled_sha256=digest(assembly), source_sha256=hashes,
                    import_adjustment='Broad Mathlib import replaced by three explicit imports; all proof bodies unchanged')
    (OUT / 'assembly.json').write_text(json.dumps(metadata, indent=2) + '\n')
    return assembly, names, hashes


def main():
    assembly, names, hashes = assemble()
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'],
                                      cwd=LEAN, text=True).strip()
    toolchain = (LEAN / 'lean-toolchain').read_text().strip().split(':v')[-1]
    if f'version {toolchain},' not in version:
        raise RuntimeError(f'Unexpected Lean toolchain: {version}')
    mathlib = LEAN / '.lake/packages/mathlib'
    revision = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'],
                                       text=True).strip()
    packages = json.loads((LEAN / 'lake-manifest.json').read_bytes())['packages']
    pinned_revision = next(p['rev'] for p in packages if p['name'] == 'mathlib')
    if revision != pinned_revision:
        raise RuntimeError(f'Unexpected Mathlib revision: {revision}')
    logpath = OUT / 'lean.log'
    started = time.monotonic()
    with logpath.open('w') as log:
        proc = subprocess.run(['lake', 'env', 'lean', '--trust=0', str(assembly)],
                              cwd=LEAN, stdout=log, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - started
    text = logpath.read_text()
    if proc.returncode != 0:
        print(text)
        return proc.returncode
    if 'sorryAx' in text or re.search(r'\b(error|warning)(\([^\n]*\))?:', text):
        raise RuntimeError('Lean audit contains a warning, error, or sorryAx; see ' + str(logpath))
    audit = {}
    for name in names:
        match = re.search("'" + re.escape(name) + r"' depends on axioms: \[(.*?)\]", text, re.S)
        if match:
            axioms = [a.strip() for a in match.group(1).split(',') if a.strip()]
        elif f"'{name}' does not depend on any axioms" in text:
            axioms = []
        else:
            raise RuntimeError(f'Missing axiom report: {name}')
        if not set(axioms) <= ALLOWED:
            raise RuntimeError(f'Unexpected axioms: {name}: {axioms}')
        audit[name] = axioms
    finite_log = OUT / 'python.log'
    with finite_log.open('w') as log:
        subprocess.run([sys.executable, '-B', str(ROOT / 'tools/projection_reachability_finite.py')],
                       check=True, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    finite = json.loads((OUT / 'python_results.json').read_text())
    if finite['lean_export']['status'] != 'PASS':
        raise RuntimeError('Lean/Python transition export comparison did not pass')
    if any(digest(ROOT / p) != sha for p, sha in hashes.items()):
        raise RuntimeError('An input changed during verification')
    result = dict(status='PASS', lean=version, mathlib_commit=revision, trust_level=0,
                  lean_exit_code=proc.returncode, lean_seconds=round(elapsed, 3),
                  assembled_sha256=digest(assembly), source_sha256=hashes,
                  audited_public_theorems=len(audit), axioms=audit,
                  lean_python_transition_matches=finite['lean_export']['total_transitions'],
                  python_systems=sum(x['systems'] for x in finite['exhaustive']),
                  python_start_cases=sum(x['starts'] for x in finite['exhaustive']))
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in {'axioms', 'source_sha256'}}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
