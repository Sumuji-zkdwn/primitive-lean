#!/usr/bin/env python3
"""Check the actual PR #142 sources and additive geometric bonding audit.

The source manifest pins the audited inputs. Generated harnesses, logs and
results go only to --output-dir. This is a dedicated check, not a replacement
for the repository's unified tools/verify.py orchestration.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'docs/verification/2026-11-17-laakso-bonding'
PARTS = [
    'FutureObservations', 'OperatorWordObservations', 'CrossSystemObservation',
    'InverseTowerObservation', 'LaaksoFiniteGraph', 'LaaksoRealization',
    'LaaksoGeometricProjection', 'LaaksoGeometricTower',
    'LaaksoNonlinearObstruction', 'LaaksoVoidRelationalBridge',
]
IMPORTS = [
    'Mathlib.Logic.Function.Iterate', 'Mathlib.Data.Fintype.Card',
    'Mathlib.Data.Fintype.Sum', 'Mathlib.Data.Fintype.Prod',
    'Mathlib.Algebra.BigOperators.Fin',
    'Mathlib.SetTheory.Cardinal.Finite', 'Mathlib.Topology.UnitInterval',
    'Mathlib.Topology.Constructions', 'Mathlib.Topology.Constructions.SumProd',
    'Mathlib.Tactic.FinCases', 'Mathlib.Tactic.NormNum', 'Mathlib.Tactic.Ring',
    'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.Positivity',
    'Mathlib.Tactic.FieldSimp',
]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', required=True, type=Path)
    ap.add_argument('--lean', default='lean', help='Lean executable or elan shim')
    ap.add_argument('--packages', type=Path, default=ROOT/'lean/.lake/packages')
    ap.add_argument('--assemble-only', action='store_true')
    args = ap.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source_manifest = json.loads((EVIDENCE/'source-manifest.json').read_text())
    for entry in source_manifest['files']:
        data = (ROOT/entry['path']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if blob != entry['sha']:
            raise SystemExit(f"Pinned source mismatch: {entry['path']}")
    preamble = ('\n'.join('import '+m for m in IMPORTS) +
                '\nset_option maxHeartbeats 2000000\nset_option maxRecDepth 4096\n').encode()
    source_dir = ROOT/'linear_input/lean_check'
    (out/'Upstream.lean').write_bytes(preamble+b'\n'.join(
        (source_dir/(part+'.inc')).read_bytes() for part in PARTS))
    (out/'LaaksoBondingAudit.lean').write_bytes(
        b'import Upstream\n'+(source_dir/'LaaksoBondingAudit.inc').read_bytes())
    print(f"Verified {len(source_manifest['files'])} pinned inputs; assembled actual sources.", flush=True)
    if args.assemble_only:
        return
    # Resolve an elan shim in the pinned project's cwd, not the output directory.
    prefix = subprocess.check_output([args.lean, '--print-prefix'], cwd=ROOT/'lean', text=True).strip()
    lean = str(Path(prefix)/'bin/lean')
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    if 'version 4.30.0-rc2,' not in version:
        raise SystemExit(f'Wrong Lean version: {version}')
    packages = args.packages.resolve()
    manifest = json.loads((ROOT/'lean/lake-manifest.json').read_text())
    revisions = {}
    for package in manifest['packages']:
        actual = subprocess.check_output(
            ['git', '-C', str(packages/package['name']), 'rev-parse', 'HEAD'], text=True).strip()
        if actual != package['rev']:
            raise SystemExit(f"Wrong dependency revision: {package['name']} {actual}")
        revisions[package['name']] = actual
    env = dict(os.environ)
    env['LEAN_PATH'] = os.pathsep.join([str(out)] + [
        str(packages/p['name']/'.lake/build/lib/lean') for p in manifest['packages']])
    results = []
    for module in ['Upstream', 'LaaksoBondingAudit']:
        cmd = [lean, '--trust=0', '-o', module+'.olean', module+'.lean']
        start = time.monotonic()
        with (out/(module+'.log')).open('w') as log_file:
            proc = subprocess.run(cmd, cwd=out, env=env,
                                  stdout=log_file, stderr=subprocess.STDOUT)
        log = (out/(module+'.log')).read_text()
        bad = 'sorryAx' in log or 'declaration uses' in log
        record = {'module': module, 'command': cmd, 'exit_code': proc.returncode,
                  'seconds': round(time.monotonic()-start, 3),
                  'sorryAx_present': 'sorryAx' in log,
                  'forbidden_proof_warning': bad,
                  'source_sha256': digest(out/(module+'.lean')),
                  'log_sha256': digest(out/(module+'.log'))}
        results.append(record)
        print(json.dumps(record), flush=True)
        if proc.returncode or bad:
            print(log, flush=True)
            break
    all_pass = len(results) == 2 and all(
        r['exit_code'] == 0 and not r['forbidden_proof_warning'] for r in results)
    summary = {'source_commit': source_manifest['source_commit'], 'compiler': version,
               'dependency_revisions': revisions, 'kernel_trust_level': 0,
               'results': results, 'all_pass': all_pass}
    (out/'lean-results.json').write_text(json.dumps(summary, indent=2)+'\n')
    raise SystemExit(0 if all_pass else 1)

if __name__ == '__main__':
    main()
