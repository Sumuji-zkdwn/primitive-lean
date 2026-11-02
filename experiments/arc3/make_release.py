"""Build the versioned, deterministic source distribution with file hashes."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
CORE = ('VERSION', 'run.py', 'check_release.py', 'make_release.py', 'QUICKSTART.md', 'pytest.ini',
        'core.py', 'learner.py', 'experiments.py', 'affine_belief.py',
        'parity_probe.py', 'trace_structure.py', 'online.py', 'arc_agent.py',
        'explore_agent.py', 'hybrid_agent.py', 'EXISTING_AGENTS.md', 'public-agent-sources.json')


def build(root, output):
    version = (root/'VERSION').read_text().strip()
    files = {name: (root/name).read_bytes() for name in CORE}
    files['README.md'] = (root/'QUICKSTART.md').read_bytes()
    for directory in ('runtime', 'vendor', 'tests', 'tests_sdk'):
        for path in sorted((root/directory).rglob('*')):
            if (path.is_file() and '__pycache__' not in path.parts
                    and path.suffix in {'.py', '.json', '.txt', '.lock'}):
                files[path.relative_to(root).as_posix()] = path.read_bytes()
    files['vendor/explore/LICENSE'] = (root/'vendor/explore/LICENSE').read_bytes()
    # Only named measurement files belong in a release, never caches or raw runs.
    for name in ('integrated-summary.json', 'integrated-metadata.json',
                 'explore-summary.json', 'explore-metadata.json',
                 'integration-public-20261027.json', 'hybrid-comparison.json'):
        files['reports/'+name] = (root/'reports'/name).read_bytes()
    manifest = {'name': 'ARC3 Explorer', 'version': version,
                'sha256': {name: hashlib.sha256(data).hexdigest()
                           for name, data in sorted(files.items())}}
    files['MANIFEST.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo('arc3-explorer-'+version+'/'+name)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    return {'path': str(output), 'version': version, 'files': len(files),
            'sha256': hashlib.sha256(output.read_bytes()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(build(ROOT, args.output), indent=2))
