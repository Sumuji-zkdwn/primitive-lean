"""Validate explicit toolchain-migration hashes without rewriting old provenance.

The migration ledger is not proof evidence. The existing Lean/axiom checkers
still compile the current sources separately.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import subprocess
import tomllib

LEDGER = 'docs/lean436/migration.json'
INTEGRATION_LEDGER = 'docs/integration/manifest.json'
CONFIG_PATHS = {'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json'}
ASSEMBLER_PATHS = {'linear_input/verify_lean.py', 'tools/verify_main_result.py'}
DERIVATION_PATHS = {'tools/deps/derivation/DirectDerivation.lean'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def migration_path(path):
    if not isinstance(path, str) or '\\' in path:
        return False
    parsed = PurePosixPath(path)
    if parsed.is_absolute() or '..' in parsed.parts or str(parsed) != path:
        return False
    return path in CONFIG_PATHS | ASSEMBLER_PATHS | DERIVATION_PATHS or (
        (path.startswith('lean/') or path.startswith('linear_input/lean_check/'))
        and parsed.suffix in {'.lean', '.inc'} and '.lake' not in parsed.parts)


def git(root, *args):
    result = subprocess.run(['git', *args], cwd=root, capture_output=True)
    if result.returncode:
        raise ValueError('Git migration source unavailable: ' + ' '.join(args))
    return result.stdout


def accepts_current_hash(migration, relative, original, current):
    """Accept an unchanged source or the exact verified old-to-new mapping."""
    if not migration.get('passed'):
        return False
    if current == original:
        return True
    row = migration.get('changes', {}).get(relative, {})
    return row.get('old_sha256') == original and row.get('new_sha256') == current


def audit(root):
    root = Path(root).resolve()
    path = root / LEDGER
    result = dict(present=path.is_file(), passed=True, changes={}, errors=[],
                  scope='Explicit current migration hashes; not a Lean proof check')
    if not result['present']:
        return result
    try:
        ledger = json.loads(path.read_text('utf-8'))
        if not isinstance(ledger, dict) or ledger.get('schema_version') != 1:
            raise ValueError('Unsupported Lean migration schema')
        commit = ledger.get('source_commit', '')
        if not isinstance(commit, str) or not re.fullmatch('[0-9a-f]{40}', commit):
            raise ValueError('Migration source_commit must be a full commit SHA')
        git(root, 'merge-base', '--is-ancestor', commit, 'HEAD')
        original_manifest = json.loads(git(root, 'show', f'{commit}:{INTEGRATION_LEDGER}'))
        current_manifest = json.loads((root / INTEGRATION_LEDGER).read_text('utf-8'))
        if original_manifest != current_manifest:
            raise ValueError('Historical integration manifest was changed during migration')
        original_rows = {row['path']: row for row in original_manifest['files']}
        target = ledger.get('target', {})
        if not isinstance(target, dict):
            raise ValueError('Invalid migration target')
        toolchain = (root / 'lean/lean-toolchain').read_text('utf-8').strip()
        if target.get('toolchain') != toolchain:
            raise ValueError('Migration target toolchain does not match current pin')
        mathlib = target.get('mathlib', '')
        if not isinstance(mathlib, str) or not re.fullmatch('[0-9a-f]{40}', mathlib):
            raise ValueError('Migration target mathlib must be a full revision SHA')
        lakefile = tomllib.loads((root / 'lean/lakefile.toml').read_text('utf-8'))
        requirements = [row for row in lakefile.get('require', []) if row.get('name') == 'mathlib']
        manifest = json.loads((root / 'lean/lake-manifest.json').read_text('utf-8'))
        packages = [row for row in manifest.get('packages', []) if row.get('name') == 'mathlib']
        if len(requirements) != 1 or len(packages) != 1 or any(
                row.get('rev') != mathlib for row in requirements + packages):
            raise ValueError('Migration target mathlib does not match Lake pins')
        changes = ledger.get('changes')
        if not isinstance(changes, list) or not changes:
            raise ValueError('Migration changes must be a nonempty list')
        accepted = {}
        for row in changes:
            if not isinstance(row, dict):
                raise ValueError('Invalid migration change record')
            relative = row.get('path')
            if not migration_path(relative):
                raise ValueError('Unapproved migration source path: ' + repr(relative))
            if relative in accepted:
                raise ValueError('Duplicate migration source: ' + relative)
            if not isinstance(row.get('reason'), str) or not row['reason'].strip():
                raise ValueError('Missing migration reason: ' + relative)
            old, new = row.get('old_sha256', ''), row.get('new_sha256', '')
            if not all(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value)
                       for value in (old, new)) or old == new:
                raise ValueError('Invalid migration hashes: ' + relative)
            current_path = (root / relative).resolve()
            if not current_path.is_relative_to(root) or not current_path.is_file():
                raise ValueError('Migration source is missing or external: ' + relative)
            if sha(git(root, 'show', f'{commit}:{relative}')) != old:
                raise ValueError('Migration original hash mismatch: ' + relative)
            if relative in original_rows and original_rows[relative]['sha256'] != old:
                raise ValueError('Migration original disagrees with retained manifest: ' + relative)
            if sha(current_path.read_bytes()) != new:
                raise ValueError('Migration current hash mismatch: ' + relative)
            accepted[relative] = row
        changed = {name for name in git(root, 'diff', '--name-only', '-z', commit, '--',
                   'lean', 'linear_input/lean_check',
                   *sorted(ASSEMBLER_PATHS | DERIVATION_PATHS)).decode('utf-8').split('\0')
                   if migration_path(name)}
        if set(accepted) != changed:
            raise ValueError('Migration coverage mismatch: ' + repr(sorted(set(accepted) ^ changed)))
        result.update(source_commit=commit, target=target, changes=accepted)
    except (OSError, ValueError, KeyError, TypeError) as error:
        result['errors'].append(str(error))
        result['passed'] = False
        result['changes'] = {}
    return result
