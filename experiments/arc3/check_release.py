"""Check distribution file hashes; optionally run its credential-free tests."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def check(root):
    manifest = json.loads((root/'MANIFEST.json').read_text(encoding='utf-8'))
    errors = []
    for name, digest in manifest['sha256'].items():
        relative = Path(name)
        if relative.is_absolute() or '..' in relative.parts:
            errors.append('Invalid manifest path: '+name)
            continue
        path = root/relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            errors.append('Missing or changed file: '+name)
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    errors = check(root)
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print('Distribution hashes: OK', flush=True)
    if args.test:
        return subprocess.call([sys.executable, '-m', 'pytest', '-q'], cwd=root)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
