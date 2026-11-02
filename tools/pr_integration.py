"""Run the PR integration checks through tools/verify.py --integration-only."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

SMOKE_TESTS = (
    'check_galois_bridge', 'check_f16_unexpected_bridges',
    'check_complementary_recovery', 'check_shear_commutator',
    'check_strange_operator_galois', 'check_f16_saddle_cantor',
    'check_f0_dynamics', 'check_future_observation', 'check_e_wfs_fenchel',
    'check_energy_gauge_fenchel', 'check_e_wfs_future_bridge',
    'check_temporal_sampling', 'check_wfs_mobius_fourier',
    'check_f0_future_minimality',
    'check_wfs_sampling',
    'check_f16_fenchel_atlas',
    'check_f16_fenchel_full',
    'check_f16_spectral',
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
    for name, args in stages:
        print('Running ' + name, flush=True)
        record = command(args, 'integration-' + name, cwd=root)
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
