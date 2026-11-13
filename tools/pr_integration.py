"""Run the PR integration checks through tools/verify.py --integration-only."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

SMOKE_TESTS = (
    'check_galois_bridge', 'check_f16_unexpected_bridges',
    'check_complementary_recovery', 'check_shear_commutator',
    'check_strange_operator_galois',
    'check_strange_operator_counting', 'check_f16_saddle_cantor',
    'check_f0_dynamics', 'check_future_observation', 'check_e_wfs_fenchel',
    'check_energy_gauge_fenchel', 'check_e_wfs_future_bridge',
    'check_temporal_sampling', 'check_wfs_mobius_fourier',
    'check_f0_future_minimality',
    'check_wfs_sampling',
    'check_curve_word_chain',
    'check_laakso_finite',
)


def run_integration(root, command, rebuild=False):
    root = Path(root)
    out = root / 'verification'
    result = dict(timestamp_utc=datetime.now(timezone.utc).isoformat(), passed=False,
                  source_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                  dirty=bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=root, text=True).strip()),
                  checks=[], errors=[], kaggle_execution=False, public_game_execution=False,
                  historical_delivery_and_rendering='not_checked')
    def save():
        (out / 'pr-integration.json').write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', 'utf-8')
    save()
    stages = [('source-audit', [sys.executable, '-B', '-X', 'utf8', 'tools/check_pr_integration.py']),
              ('repository-tests', [sys.executable, '-B', '-X', 'utf8', '-m', 'unittest', 'discover', '-s', 'tests', '-v'])]
    stages += [(name, [sys.executable, '-B', '-X', 'utf8', f'tools/{name}.py']) for name in SMOKE_TESTS]
    stages += [('arc3-offline', [sys.executable, '-B', '-X', 'utf8', 'tools/verify.py', '--arc3-only'])]
    proof_command = [sys.executable, '-B', '-X', 'utf8', 'tools/verify.py', '--proof-only']
    if rebuild:
        proof_command.append('--rebuild')
    stages.append(('proof-only', proof_command))
    # Independent Lean modules outside the joint checker: trust-zero compilation and
    # axiom audits, identical to the separate CI steps. They run after proof-only
    # because --rebuild clears lean/.lake/build.
    lean = root / 'lean'
    stages += [('build-elastica', ['lake', 'build', 'Elastica'], lean),
               ('moving-curve', ['lake', 'env', 'lean', '--trust=0', 'MovingCurve.lean',
                                 '-o', '.lake/build/lib/lean/MovingCurve.olean'], lean),
               ('moving-curve-audit', ['lake', 'env', 'lean', '--trust=0', 'MovingCurveAudit.lean'], lean),
               ('okanohara-bridge', [sys.executable, '-B', '-X', 'utf8', 'tools/verify_okanohara_bridge.py']),
               ('finite-markov-transport', [sys.executable, '-B', '-X', 'utf8', 'tools/verify_finite_markov_transport.py'])]
    for name, args, *cwd in stages:
        print('Running ' + name, flush=True)
        record = command(args, 'integration-' + name, cwd=cwd[0] if cwd else root)
        result['checks'].append(dict(name=name, **record))
        if record['exit_code']:
            result['errors'].append(name + ' failed; see ' + record['log'])
            save()
            return result
        save()
    proof = json.loads((out/'proof-only.json').read_text('utf-8'))
    result.update(passed=proof['passed'], theorem_count=proof['theorem_count'],
                  declaration_count=proof['declaration_count'])
    save()
    return result
