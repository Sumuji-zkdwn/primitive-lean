"""Check retained source bytes and complete registration of integrated proofs.

The manifest records source commits separately from adapted working hashes.
This is a source/provenance audit; Lean proof validity is checked separately.
"""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def assignment(path, name):
    tree = ast.parse(path.read_text('utf-8'))
    matches = [n for n in ast.walk(tree) if isinstance(n, ast.Assign)
               and any(isinstance(t, ast.Name) and t.id == name for t in n.targets)]
    if len(matches) != 1:
        raise ValueError(f'{path}: expected one {name} assignment')
    return ast.literal_eval(matches[0].value)


def audit(root=ROOT):
    manifest = json.loads((root / 'docs/integration/manifest.json').read_text('utf-8'))
    errors = ['Unresolved manifest construction error: ' + error
              for error in manifest.get('construction_errors', [])]
    rows = manifest['files']
    retained_paths = [row['path'] for row in rows]
    if len(retained_paths) != len(set(retained_paths)):
        errors.append('Duplicate retained source path')
    by_path = {row['path']: row for row in rows}
    baseline_paths = set(manifest.get('baseline_paths', []))
    baseline_rows = {row['path'] for row in rows
                     if row.get('role') == 'baseline_proof_or_configuration'}
    if not baseline_paths or baseline_paths != baseline_rows:
        errors.append('Baseline provenance coverage mismatch: ' +
                      repr(sorted(baseline_paths ^ baseline_rows)))
    for row in rows:
        original = row.get('original_sha256')
        adaptations = row.get('permitted_adaptations', [])
        if row['path'] in baseline_paths:
            if (row.get('source_commit') != manifest.get('baseline_commit') or
                    row.get('source_path') != row['path'] or
                    not original or row['sha256'] != original or adaptations or
                    row.get('byte_identical') is not True):
                errors.append('Baseline source cannot be adapted: ' + row['path'])
        if row.get('byte_identical') is True:
            if not original or row['sha256'] != original or adaptations:
                errors.append('Byte-identical provenance is inconsistent: ' + row['path'])
        elif (row.get('role') not in {'explicit_source_adapter', 'adapted_retained_source'} or
              not adaptations or not all(isinstance(a, str) and a.strip() for a in adaptations)):
            errors.append('Changed source lacks explicit permitted adaptations: ' + row['path'])
        if original is None:
            sources = row.get('source_files', [])
            if row.get('role') != 'explicit_source_adapter' or not sources:
                errors.append('Missing original source provenance: ' + row['path'])
            for source in sources:
                preserved = by_path.get(source.get('preserved_copy'))
                if (not preserved or preserved.get('original_sha256') != source.get('original_sha256') or
                        preserved.get('sha256') != source.get('original_sha256') or
                        preserved.get('byte_identical') is not True):
                    errors.append('Adapter original is not preserved: ' + row['path'])
    for row in rows:
        path = root / row['path']
        if not path.is_file():
            errors.append('Missing retained source: ' + row['path'])
        elif hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
            errors.append('Retained source hash mismatch: ' + row['path'])
    registry = assignment(root / 'tools/verify_main_result.py', 'SUPPLEMENTS')
    scopes = assignment(root / 'tools/verify.py', 'supplemental_scopes')
    original_parts = set(assignment(root / 'linear_input/verify_lean.py', 'PARTS'))
    paths = [path for path, _ in registry]
    namespaces = [ns for _, ns in registry]
    if len(paths) != len(set(paths)) or len(namespaces) != len(set(namespaces)):
        errors.append('Duplicate supplemental source or namespace')
    for path in paths:
        if not (root / path).is_file():
            errors.append('Missing registered supplement: ' + path)
        if not scopes.get(Path(path).stem):
            errors.append('Missing descriptive scope: ' + path)
    candidates = {p.relative_to(root).as_posix()
                  for p in (root / 'linear_input/lean_check').glob('*.inc')
                  if p.name not in original_parts}
    if candidates != set(paths):
        errors.append('Supplement registration mismatch: ' + repr(sorted(candidates ^ set(paths))))
    covered = {row['path'] for row in manifest['files']}
    if not set(paths) <= covered:
        errors.append('Missing supplement provenance: ' + repr(sorted(set(paths) - covered)))
    return dict(passed=not errors, errors=errors, retained_files=len(manifest['files']),
                supplemental_groups=len(registry), scope='Source bytes and registration, not proof validity')


if __name__ == '__main__':
    result = audit()
    out = ROOT / 'verification'
    out.mkdir(exist_ok=True)
    (out / 'pr-source-audit.json').write_text(json.dumps(result, indent=2) + '\n', 'utf-8')
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['passed'] else 1)
