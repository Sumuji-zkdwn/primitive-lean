#!/usr/bin/env python3
"""Reproduce the PR #111 shell argument boundary without invoking Lean.

The tiny fake `lean` reports arguments. This tests shell parsing only; it does not
prove anything about Lean compilation or the full dependency extractor.
"""
import os
from pathlib import Path
import subprocess
import tempfile


def run():
    with tempfile.TemporaryDirectory(prefix='handoff-probe-') as temp:
        root = Path(temp)
        bindir = root / 'bin'
        bindir.mkdir()
        fake = bindir / 'lean'
        fake.write_text('#!/bin/sh\nprintf "LEAN_PATH=<%s>\\n" "$LEAN_PATH"\nprintf "ARG=<%s>\\n" "$@"\n', encoding='utf-8')
        fake.chmod(0o755)
        env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ.get('PATH', ''), LEAN_PATH='/prior')
        plain = root / 'work'
        spaced = root / 'work with spaces'
        plain.mkdir()
        spaced.mkdir()

        def current(work):
            # These interpolations mirror pr_kernel.py at fb049ad, but execute a fake lean.
            lp = f'LEAN_PATH={work}:$LEAN_PATH'
            command = f'{lp} lean --root={work} -o {work}/ExtraProbe.olean {work}/ExtraProbe.lean'
            return subprocess.run(['sh', '-c', command], env=env, text=True, capture_output=True)

        baseline = current(plain)
        problematic = current(spaced)
        safe_env = dict(env, LEAN_PATH=str(spaced) + os.pathsep + env['LEAN_PATH'])
        safe = subprocess.run(['lean', f'--root={spaced}', '-o', str(spaced / 'ExtraProbe.olean'),
                               str(spaced / 'ExtraProbe.lean')], env=safe_env, text=True, capture_output=True)
        assert baseline.returncode == 0, baseline.stderr
        assert problematic.returncode != 0, 'Expected shell splitting for the space-containing path'
        assert safe.returncode == 0, safe.stderr
        assert f'LEAN_PATH=<{spaced}:/prior>' in safe.stdout
        assert f'ARG=<--root={spaced}>' in safe.stdout
        print('PASS: unquoted form works with a path without spaces')
        print(f'PASS: same form fails with spaces (exit {problematic.returncode})')
        print('PASS: argument-list plus environment preserves the path with spaces')
        print('Scope: fake executable and shell parsing only; no Lean proof was checked.')


if __name__ == '__main__':
    run()
