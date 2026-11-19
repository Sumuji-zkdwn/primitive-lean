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
POST_MIGRATION = 'docs/lean436/post-migration.json'
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


def check_retained_manifest(original, current):
    """Keep each historical ledger entry; new rows undergo normal source auditing."""
    fixed_fields = set(original) | set(current)
    for key in fixed_fields - {'files', 'post_snapshot_additions'}:
        if key not in original or key not in current or original[key] != current[key]:
            raise ValueError('Historical integration manifest was changed: ' + key)
    original_paths = {row['path'] for row in original['files']}
    rows = current['files']
    if [r for r in rows if r['path'] in original_paths] != original['files']:
        raise ValueError('Historical integration manifest was changed: files')
    paths = {row['path'] for row in rows}
    if len(paths) != len(rows):
        raise ValueError('Duplicate retained source path')
    for path in paths - original_paths:
        rel = PurePosixPath(path)
        if rel.is_absolute() or '..' in rel.parts or str(rel) != path or '\\' in path or ':' in path:
            raise ValueError('Invalid new integration source path: ' + path)
    original_notes = original.get('post_snapshot_additions', [])
    current_notes = current.get('post_snapshot_additions', [])
    if (current_notes[:len(original_notes)] != original_notes or
            any(n['path'] not in paths - original_paths for n in current_notes[len(original_notes):])):
        raise ValueError('Historical integration manifest was changed: post_snapshot_additions')


def post_migration_changes(root, commit):
    """Pin later edits independently against a committed copy of the migration."""
    path = root / POST_MIGRATION
    if not path.is_file():
        return {}
    data = json.loads(path.read_bytes())
    anchor = data['migration_commit']
    if data.get('schema_version') != 1 or not isinstance(anchor, str) or not re.fullmatch('[0-9a-f]{40}', anchor):
        raise ValueError('Invalid post-migration ledger or anchor')
    git(root, 'merge-base', '--is-ancestor', commit, anchor)
    git(root, 'merge-base', '--is-ancestor', anchor, 'HEAD')
    if git(root, 'show', f'{anchor}:{LEDGER}') != (root / LEDGER).read_bytes():
        raise ValueError('The post-migration anchor must retain the exact migration ledger')
    rows = {}
    for row in data['changes']:
        relative = row['path']
        if (not migration_path(relative) or relative in CONFIG_PATHS or relative in rows or
                not isinstance(row.get('reason'), str) or not row['reason'].strip()):
            raise ValueError('Invalid post-migration change: ' + str(relative))
        migrated = sha(git(root, 'show', f'{anchor}:{relative}'))
        current = (root / relative).resolve()
        if (not current.is_relative_to(root) or not current.is_file() or
                row['migration_sha256'] != migrated or row['current_sha256'] != sha(current.read_bytes()) or
                migrated == row['current_sha256']):
            raise ValueError('Post-migration hash mismatch: ' + relative)
        rows[relative] = row
    return rows


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
        check_retained_manifest(original_manifest, current_manifest)
        subsequent = post_migration_changes(root, commit)
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
            after = subsequent.get(relative)
            if after and after['migration_sha256'] != new:
                raise ValueError('Post-migration change does not start at the recorded migration: ' + relative)
            effective = after['current_sha256'] if after else new
            if sha(current_path.read_bytes()) != effective:
                raise ValueError('Migration current hash mismatch: ' + relative)
            accepted[relative] = dict(row, new_sha256=effective)
        for relative, after in subsequent.items():
            if relative not in accepted:
                old = sha(git(root, 'show', f'{commit}:{relative}'))
                if after['migration_sha256'] != old:
                    raise ValueError('Unrecorded migration before later change: ' + relative)
                accepted[relative] = dict(path=relative, old_sha256=old, new_sha256=after['current_sha256'],
                                          reason=after['reason'])
        # Only paths retained from the source commit have an old migration hash.
        # New modules belong to normal registration/proof checks. Disable rename
        # detection so a renamed retained source still exposes its deletion.
        changed = {name for name in git(root, 'diff', '--no-renames', '--diff-filter=MDT',
                   '--name-only', '-z', commit, '--',
                   'lean', 'linear_input/lean_check',
                   *sorted(ASSEMBLER_PATHS | DERIVATION_PATHS)).decode('utf-8').split('\0')
                   if migration_path(name)}
        effective_changes = {p for p, row in accepted.items() if row['old_sha256'] != row['new_sha256']}
        if effective_changes != changed:
            raise ValueError('Migration coverage mismatch: ' + repr(sorted(effective_changes ^ changed)))
        result.update(source_commit=commit, target=target, changes=accepted, post_migration_changes=subsequent)
    except (OSError, ValueError, KeyError, TypeError) as error:
        result['errors'].append(str(error))
        result['passed'] = False
        result['changes'] = {}
    return result
