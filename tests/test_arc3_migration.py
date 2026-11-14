"""Exercise historical ARC provenance through real local Git migration fixtures."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('arc3_integration', ROOT / 'tools/arc3_integration.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class ArcMigrationAudit(unittest.TestCase):
    @staticmethod
    def git_at(root, *args):
        return subprocess.check_output(['git', *args], cwd=root, stderr=subprocess.PIPE).decode().strip()

    @staticmethod
    def write_at(root, relative, data):
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data.encode('utf-8') if isinstance(data, str) else data)

    @classmethod
    def setUpClass(cls):
        cls.fixture = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.fixture.cleanup)
        root = Path(cls.fixture.name)
        cls.git_at(root, 'init', '-q')
        cls.git_at(root, 'config', 'user.email', 'fixture@example.invalid')
        cls.git_at(root, 'config', 'user.name', 'ARC provenance fixture')
        cls.git_at(root, 'config', 'core.autocrlf', 'false')
        cls.paths = [f'lean/Fixture{i:02d}.lean' for i in range(61)]
        for i, path in enumerate(cls.paths):
            cls.write_at(root, path, ''.join(
                f'theorem retained_{j} : True := True.intro\n' for j in range(i, 475, 61)))
        cls.git_at(root, 'add', '.')
        cls.git_at(root, 'commit', '-qm', 'Pinned source snapshot')
        ref = cls.git_at(root, 'rev-parse', 'HEAD')
        blobs = {path: CHECK.blob_sha((root / path).read_bytes()) for path in cls.paths}
        index = {'ref': ref, 'groups': dict(elastica=214, linear=251, main=10),
                 'sources': [{'path': path, 'sha': blobs[path]} for path in cls.paths],
                 'theorems': [{'path': cls.paths[j % 61], 'source_sha': blobs[cls.paths[j % 61]],
                               'name': f'retained_{j}', 'statement': f'theorem retained_{j} : True'}
                              for j in range(475)]}
        cls.write_at(root, CHECK.INDEX, json.dumps(index))
        cls.write_at(root, 'docs/integration/manifest.json', json.dumps({
            'files': [{'path': path, 'sha256': hashlib.sha256((root / path).read_bytes()).hexdigest()}
                      for path in cls.paths]}))
        cls.write_at(root, 'lean/lean-toolchain', 'leanprover/lean4:v4.36.0-rc2\n')
        cls.write_at(root, 'lean/lakefile.toml',
                     'name = "fixture"\n[[require]]\nname = "mathlib"\nrev = "' + 'b' * 40 + '"\n')
        cls.write_at(root, 'lean/lake-manifest.json', json.dumps({
            'packages': [{'name': 'mathlib', 'rev': 'b' * 40}]}))
        cls.git_at(root, 'add', '.')
        cls.git_at(root, 'commit', '-qm', 'Retained ARC inventory and migration base')

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        shutil.copytree(self.fixture.name, self.root)
        self.index_bytes = (self.root / CHECK.INDEX).read_bytes()

    def git(self, *args):
        return self.git_at(self.root, *args)

    def write(self, relative, data):
        self.write_at(self.root, relative, data)

    def migrate(self):
        relative = self.paths[0]
        old = (self.root / relative).read_bytes()
        current = old + b'-- proof syntax adapted for the new toolchain\n'
        self.write(relative, current)
        ledger = {'schema_version': 1, 'source_commit': self.git('rev-parse', 'HEAD'),
                  'target': {'toolchain': 'leanprover/lean4:v4.36.0-rc2', 'mathlib': 'b' * 40},
                  'changes': [{'path': relative, 'old_sha256': hashlib.sha256(old).hexdigest(),
                               'new_sha256': hashlib.sha256(current).hexdigest(),
                               'reason': 'Compatibility proof syntax; historical inventory retained.'}]}
        self.write(CHECK.MIGRATION.LEDGER, json.dumps(ledger))
        return ledger

    def reject(self, message):
        result = CHECK.source_audit(self.root)
        self.assertFalse(result['passed'], result)
        self.assertTrue(any(message in error for error in result['errors']), result)

    def commit_index(self, index):
        self.write(CHECK.INDEX, json.dumps(index))
        self.git('add', CHECK.INDEX)
        self.git('commit', '-qm', 'Inventory fixture variant')

    def test_unchanged_historical_inventory_passes_without_migration(self):
        result = CHECK.source_audit(self.root)
        self.assertTrue(result['passed'], result)
        self.assertEqual((result['sources'], result['theorems']), (61, 475))
        self.assertTrue(all(row['byte_identical'] for row in result['source_provenance']))

    def test_exact_migration_preserves_index_and_records_both_hashes(self):
        self.migrate()
        result = CHECK.source_audit(self.root)
        self.assertTrue(result['passed'], result)
        self.assertEqual((self.root / CHECK.INDEX).read_bytes(), self.index_bytes)
        migrated = [row for row in result['source_provenance'] if row['migration_verified']]
        self.assertEqual([row['path'] for row in migrated], [self.paths[0]])
        self.assertNotEqual(migrated[0]['original_sha256'], migrated[0]['current_sha256'])
        self.assertNotEqual(migrated[0]['original_git_blob_sha1'], migrated[0]['current_git_blob_sha1'])

    def test_index_cannot_be_rewritten_to_current_migrated_hashes(self):
        self.migrate()
        index = json.loads(self.index_bytes)
        current_blob = CHECK.blob_sha((self.root / self.paths[0]).read_bytes())
        index['sources'][0]['sha'] = current_blob
        for row in index['theorems']:
            if row['path'] == self.paths[0]:
                row['source_sha'] = current_blob
        self.write(CHECK.INDEX, json.dumps(index))
        self.reject('Historical ARC theorem index was changed')

    def test_committed_inventory_must_match_actual_old_git_blob(self):
        index = json.loads(self.index_bytes)
        index['sources'][0]['sha'] = 'a' * 40
        for row in index['theorems']:
            if row['path'] == self.paths[0]:
                row['source_sha'] = 'a' * 40
        self.commit_index(index)
        self.migrate()
        self.reject('Pinned original blob differs from inventory')

    def test_unrecorded_source_edit_is_rejected(self):
        self.migrate()
        self.write(self.paths[1], '-- edit missing from the migration ledger\n')
        self.reject('Migration coverage mismatch')

    def test_further_edit_to_a_recorded_source_is_rejected(self):
        self.migrate()
        self.write(self.paths[0], '-- edit after recording the approved hash\n')
        self.reject('Migration current hash mismatch')

    def test_ledger_old_hash_must_be_the_index_ref_source(self):
        # An otherwise valid B -> C ledger must not reinterpret an inventory
        # that still names earlier source A as if it had named B.
        self.write(self.paths[0], '-- intermediate source B\n')
        manifest_path = 'docs/integration/manifest.json'
        manifest = json.loads((self.root / manifest_path).read_bytes())
        manifest['files'][0]['sha256'] = hashlib.sha256((self.root / self.paths[0]).read_bytes()).hexdigest()
        self.write(manifest_path, json.dumps(manifest))
        self.git('add', self.paths[0], manifest_path)
        self.git('commit', '-qm', 'Different source before the toolchain migration')
        self.migrate()
        self.assertTrue(CHECK.MIGRATION.audit(self.root)['passed'])
        self.reject('Source differs from pinned inventory without a verified migration')

    def test_missing_pinned_source_commit_is_rejected(self):
        index = json.loads(self.index_bytes)
        index['ref'] = 'f' * 40
        self.commit_index(index)
        self.migrate()
        self.reject('Git migration source unavailable')


if __name__ == '__main__':
    unittest.main()
