"""Check the ARC experiment and links to existing proof sources, without Lean."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import re
import subprocess
import sys


INDEX = 'experiments/arc3/theorems475/index.json'
_MIGRATION_SPEC = importlib.util.spec_from_file_location(
    'arc3_lean_migration', Path(__file__).with_name('check_lean_migration.py'))
MIGRATION = importlib.util.module_from_spec(_MIGRATION_SPEC)
_MIGRATION_SPEC.loader.exec_module(MIGRATION)


def blob_sha(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def source_audit(root):
    root = Path(root).resolve()
    errors = []
    result = {'passed': False, 'errors': errors, 'sources': 0, 'theorems': 0,
              'source_provenance': [],
              'scope': 'Preserved historical index and Git blobs, exact verified migration hashes '
                       'and inventory counts only; not proof verification'}
    try:
        migration = MIGRATION.audit(root)
        result['migration_audit'] = migration
        if not migration['passed']:
            errors.extend('Migration: '+error for error in migration['errors'])
            return result
        raw_index = (root/INDEX).read_bytes()
        index = json.loads(raw_index)
        # The inventory was authored after its source ref. Preserve the index
        # at the migration base, then independently check its older source ref.
        index_ref = migration.get('source_commit', 'HEAD')
        if raw_index != MIGRATION.git(root, 'show', f'{index_ref}:{INDEX}'):
            errors.append('Historical ARC theorem index was changed')
        result.update(sources=len(index['sources']), theorems=len(index['theorems']),
                      ref=index['ref'], index_ref=index_ref,
                      index_sha256=MIGRATION.sha(raw_index))
        if not isinstance(index['ref'], str) or not re.fullmatch('[0-9a-f]{40}', index['ref']):
            raise ValueError('Inventory ref must be a full commit SHA')
        if len(index['theorems']) != 475 or index['groups'] != dict(elastica=214, linear=251, main=10):
            errors.append('Unexpected theorem inventory counts')
        if len({(t['path'], t['name']) for t in index['theorems']}) != 475:
            errors.append('Duplicate theorem inventory entries')
        sources = {source['path']: source['sha'] for source in index['sources']}
        if len(index['sources']) != 61 or len(sources) != 61:
            errors.append('Unexpected or duplicate source inventory entries')
        if any(sources.get(t['path']) != t['source_sha'] for t in index['theorems']):
            errors.append('Theorem source hash disagrees with source inventory')
        for relative, expected_blob in sources.items():
            p = (root/relative).resolve()
            if (not MIGRATION.migration_path(relative) or p.suffix not in {'.lean', '.inc'}
                    or not p.is_relative_to(root)):
                errors.append('Invalid inventory source path: '+relative)
                continue
            if not p.is_file():
                errors.append('Missing source: '+relative)
                continue
            original = MIGRATION.git(root, 'show', f"{index['ref']}:{relative}")
            if blob_sha(original) != expected_blob:
                errors.append('Pinned original blob differs from inventory: '+relative)
                continue
            current = p.read_bytes()
            old_sha, new_sha = MIGRATION.sha(original), MIGRATION.sha(current)
            accepted = MIGRATION.accepts_current_hash(migration, relative, old_sha, new_sha)
            if not accepted:
                errors.append('Source differs from pinned inventory without a verified migration: '+relative)
            result['source_provenance'].append({
                'path': relative, 'original_git_blob_sha1': expected_blob,
                'current_git_blob_sha1': blob_sha(current),
                'original_sha256': old_sha, 'current_sha256': new_sha,
                'byte_identical': current == original,
                'migration_verified': current != original and accepted})
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append(str(error))
    result['passed'] = not errors
    return result


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
