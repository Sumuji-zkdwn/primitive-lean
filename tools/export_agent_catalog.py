#!/usr/bin/env python3
"""Export a commit-pinned *lexical* Lean declaration catalog as JSONL.

This is not a proof checker. It never marks declarations as kernel-verified.
Source content is read from an immutable Git tree, never the worktree.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE_PATH = re.compile(r"^lean/.*\.lean$|^linear_input/lean_check/[^/]+\.(?:lean|inc)$")
DECL = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class)\s+"
    r"(?P<name>[^\s(:{]+)"
)


def git(repo: Path, *args: str) -> bytes:
    proc = subprocess.run(["git", "-C", str(repo), *args], capture_output=True)
    if proc.returncode:
        raise ValueError(f"git {' '.join(args)} failed: {proc.stderr.decode('utf-8', 'replace').strip()}")
    return proc.stdout


def pinned_commit(repo: Path, ref: str) -> str:
    commit = git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}").decode("ascii").strip()
    if not re.fullmatch(r"[0-9a-f]{40,64}", commit):
        raise ValueError("Git returned an invalid commit SHA")
    return commit


def mask_lean(src: str) -> str:
    """Mask nested comments, line comments and string literals; preserve offsets."""
    out = list(src)
    i = depth = 0
    in_string = False
    while i < len(src):
        pair, char = src[i:i+2], src[i]
        if depth:
            if pair == '/-':
                depth += 1
                out[i:i+2] = '  '
                i += 2
                continue
            if pair == '-/':
                depth -= 1
                out[i:i+2] = '  '
                i += 2
                continue
            if char != '\n':
                out[i] = ' '
        elif in_string:
            if char == '\\' and i + 1 < len(src):
                out[i:i+2] = '  '
                i += 2
                continue
            if char == '"':
                in_string = False
            if char != '\n':
                out[i] = ' '
        elif pair == '--':
            end = src.find('\n', i)
            end = len(src) if end == -1 else end
            out[i:end] = ' ' * (end - i)
            i = end
            continue
        elif pair == '/-':
            depth = 1
            out[i:i+2] = '  '
            i += 2
            continue
        elif char == '"':
            in_string = True
            out[i] = ' '
        i += 1
    return ''.join(out)


def extract_declarations(src: str, path: str, commit: str) -> list[dict]:
    masked = mask_lean(src)
    matches = list(DECL.finditer(masked))
    digest = hashlib.sha256(src.encode('utf-8')).hexdigest()
    records = []
    for index, match in enumerate(matches):
        start = match.start()
        limit = matches[index+1].start() if index+1 < len(matches) else len(src)
        # := may be absent (e.g. a structure) or beyond the preview limit.
        assignment = masked.find(':=', match.end(), limit)
        header_end = assignment if assignment != -1 else min(limit, start + 600)
        preview = src[start:min(header_end, start+600)].strip()
        records.append({
            'source_commit': commit,
            'path': path,
            'line': src.count('\n', 0, start) + 1,
            'kind': match.group('kind'),
            'declared_name': match.group('name'),
            'header_preview': preview,
            'header_complete': assignment != -1 and header_end <= start+600,
            'file_sha256': digest,
            'verification_status': 'not_assessed',
        })
    return records


def export(repo: Path, ref: str = 'HEAD') -> tuple[bytes, bytes]:
    commit = pinned_commit(repo, ref)
    paths = [p for p in git(repo, 'ls-tree', '-r', '-z', '--name-only', commit).decode('utf-8').split('\0')
             if SOURCE_PATH.fullmatch(p) and '.lake/' not in p]
    items = []
    for path in sorted(paths):
        src = git(repo, 'show', f'{commit}:{path}').decode('utf-8')
        items.extend(extract_declarations(src, path, commit))
    items.sort(key=lambda r: (r['path'], r['line'], r['kind'], r['declared_name']))
    jsonl = ''.join(json.dumps(rec, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n'
                    for rec in items).encode('utf-8')
    counts = Counter(rec['kind'] for rec in items)
    manifest = {
        'schema_version': 1,
        'source_commit': commit,
        'source_files_scanned': len(paths),
        'lexical_declaration_count': len(items),
        'count_by_kind': dict(sorted(counts.items())),
        'jsonl_sha256': hashlib.sha256(jsonl).hexdigest(),
        'scope': 'Lexically extracted declarations from a pinned Git tree; no Lean elaboration, axiom audit or per-declaration verification',
        'verification_status': 'not_assessed',
        'excluded': 'non-named examples and non-source files',
    }
    manifest_bytes = (json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + '\n').encode('utf-8')
    return jsonl, manifest_bytes


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=ROOT)
    parser.add_argument('--ref', default='HEAD', help='Git commit/tag/branch to read (not the worktree)')
    parser.add_argument('--out-dir', type=Path, required=True)
    parser.add_argument('--check', action='store_true', help='Fail if existing output differs; do not write')
    args = parser.parse_args(argv)
    try:
        jsonl, manifest = export(args.repo, args.ref)
        outputs = {
            args.out_dir / 'declarations.jsonl': jsonl,
            args.out_dir / 'manifest.json': manifest,
        }
        if args.check:
            differences = [str(path) for path, expected in outputs.items()
                           if not path.is_file() or path.read_bytes() != expected]
            if differences:
                print('Catalog is missing or stale: ' + ', '.join(differences), file=sys.stderr)
                return 1
        else:
            args.out_dir.mkdir(parents=True, exist_ok=True)
            for path, data in outputs.items():
                path.write_bytes(data)
        print('Catalog checked' if args.check else f'Catalog written to {args.out_dir}')
        return 0
    except (ValueError, OSError, UnicodeDecodeError) as exc:
        print(f'Catalog export failed: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
