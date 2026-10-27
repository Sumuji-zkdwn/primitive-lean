"""Check the ARC experiment and links to existing proof sources, without Lean."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess
import sys


def source_audit(root):
    index = json.loads((root/'experiments/arc3/theorems475/index.json').read_text())
    errors = []
    if len(index['theorems']) != 475 or index['groups'] != dict(elastica=214, linear=251, main=10):
        errors.append('Unexpected theorem inventory counts')
    if len({(t['path'], t['name']) for t in index['theorems']}) != 475:
        errors.append('Duplicate theorem inventory entries')
    for source in index['sources']:
        p = root/source['path']
        if not p.is_file():
            errors.append('Missing source: '+source['path'])
            continue
        data = p.read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if blob != source['sha']:
            errors.append('Source differs from pinned inventory: '+source['path'])
    return {'passed': not errors, 'errors': errors, 'sources': len(index['sources']),
            'theorems': len(index['theorems']), 'ref': index['ref'],
            'scope': 'Source blob identities and inventory counts only; not proof verification'}


def run_arc3(root):
    exp = root/'experiments/arc3'
    audit = source_audit(root)
    test = subprocess.run([sys.executable, '-m', 'pytest', '-q'], cwd=exp,
                          capture_output=True, text=True, encoding='utf-8', errors='replace')
    report = {'timestamp_utc': datetime.now(timezone.utc).isoformat(),
              'passed': audit['passed'] and test.returncode == 0,
              'source_audit': audit, 'tests_exit_code': test.returncode,
              'test_output': test.stdout+test.stderr,
              'lean_rechecked': False, 'games_rerun': False}
    (exp/'reports').mkdir(exist_ok=True)
    (exp/'reports/integration-check.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    return report
