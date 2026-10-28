from pathlib import Path
import zipfile

from check_release import check
from make_release import build

ROOT = Path(__file__).resolve().parents[1]
VERSION = (ROOT/'VERSION').read_text().strip()


def test_distribution_is_reproducible_and_contains_no_run_or_cache_data(tmp_path):
    a, b = tmp_path/'a.zip', tmp_path/'b.zip'
    first, second = build(ROOT, a), build(ROOT, b)
    assert first['sha256'] == second['sha256']
    with zipfile.ZipFile(a) as archive:
        names = archive.namelist()
        assert any(n.endswith('/vendor/explore/LICENSE') for n in names)
        assert not any('/runs/' in n or '__pycache__' in n or n.endswith('.env') for n in names)
        archive.extractall(tmp_path/'unpacked')
    unpacked = tmp_path/f'unpacked/arc3-explorer-{VERSION}'
    assert check(unpacked) == []
    (unpacked/'run.py').write_text('changed')
    assert check(unpacked) == ['Missing or changed file: run.py']


def test_unpack_contains_the_default_agent_and_its_runtime(tmp_path):
    output = tmp_path/'release.zip'
    build(ROOT, output)
    with zipfile.ZipFile(output) as archive:
        for path in ('run.py', 'explore_agent.py', 'hybrid_agent.py', 'online.py', 'runtime/arc3/evaluate.py',
                     'vendor/explore/compat.py', 'VERSION', 'README.md', 'QUICKSTART.md'):
            assert f'arc3-explorer-{VERSION}/'+path in archive.namelist()
