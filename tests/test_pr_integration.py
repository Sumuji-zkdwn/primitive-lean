"""Exercise provenance and registration failure paths without running Lean."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('check_pr_integration', ROOT / 'tools/check_pr_integration.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class SourceIntegrationAudit(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write('lean/Elastica.lean', 'namespace Elastica\nend Elastica\n')
        self.write('linear_input/lean_check/Base.inc', '-- original assembly fragment\n')
        self.write('linear_input/lean_check/Proof.inc', 'namespace Example\ntheorem retained : True := True.intro\nend Example\n')
        self.write('linear_input/verify_lean.py', "PARTS = ('Base.inc',)\n")
        self.write('tools/verify_main_result.py', "SUPPLEMENTS = (('linear_input/lean_check/Proof.inc', 'Example'),)\n")
        self.write('tools/verify.py', "supplemental_scopes = {'Proof': 'A retained proposition'}\n")
        self.manifest = {
            'schema_version': 1,
            'baseline_commit': 'a' * 40,
            'baseline_paths': ['lean/Elastica.lean'],
            'construction_errors': [],
            'files': [self.row('lean/Elastica.lean', 'baseline_proof_or_configuration'),
                      self.row('linear_input/lean_check/Proof.inc', 'retained_source')],
        }
        self.save_manifest()

    def write(self, path, text):
        dest = self.root / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text, encoding='utf-8', newline='\n')

    def row(self, path, role):
        digest = hashlib.sha256((self.root / path).read_bytes()).hexdigest()
        return dict(path=path, sha256=digest, original_sha256=digest, role=role,
                    source_commit='a' * 40, source_path=path, source_pr=3,
                    byte_identical=True, permitted_adaptations=[])

    def save_manifest(self):
        self.write('docs/integration/manifest.json', json.dumps(self.manifest))

    def assert_rejected(self, expected):
        result = CHECK.audit(self.root)
        self.assertFalse(result['passed'], result)
        self.assertTrue(any(expected in error for error in result['errors']), result)

    def test_complete_retained_fixture_passes(self):
        result = CHECK.audit(self.root)
        self.assertTrue(result['passed'], result)
        self.assertEqual(result['retained_files'], 2)
        self.assertEqual(result['supplemental_groups'], 1)

    def test_changed_proof_bytes_are_rejected(self):
        self.write('linear_input/lean_check/Proof.inc', '-- altered proof\n')
        self.assert_rejected('Retained source hash mismatch')

    def test_missing_baseline_file_is_rejected(self):
        (self.root / 'lean/Elastica.lean').unlink()
        self.assert_rejected('Missing retained source')

    def test_unregistered_proof_cannot_disappear_from_audit(self):
        self.write('tools/verify_main_result.py', 'SUPPLEMENTS = ()\n')
        self.assert_rejected('Supplement registration mismatch')

    def test_registered_proof_requires_provenance(self):
        self.manifest['files'] = self.manifest['files'][:1]
        self.save_manifest()
        self.assert_rejected('Missing supplement provenance')

    def test_new_fragment_requires_registration(self):
        self.write('linear_input/lean_check/Unregistered.inc', '-- new source\n')
        self.assert_rejected('Supplement registration mismatch')

    def test_duplicate_namespace_is_rejected(self):
        self.write('tools/verify_main_result.py',
                   "SUPPLEMENTS = (('linear_input/lean_check/Proof.inc', 'Example'), "
                   "('linear_input/lean_check/Base.inc', 'Example'))\n")
        self.assert_rejected('Duplicate supplemental source or namespace')

    def test_verified_astra_sources_can_share_a_namespace(self):
        pairs = [('AstraFirst.inc', 'KerrKoopman.Shared'), ('AstraSecond.inc', 'KerrKoopman.Shared')]
        self.assertEqual(CHECK.duplicate_namespace_errors(pairs, set(pairs)), [])

    def test_shared_namespace_requires_every_exact_verified_pair(self):
        pairs = [('AstraFirst.inc', 'KerrKoopman.Shared'), ('Unverified.inc', 'KerrKoopman.Shared')]
        self.assertTrue(CHECK.duplicate_namespace_errors(pairs, {pairs[0]}))

    def test_filename_prefix_does_not_authorize_shared_namespace(self):
        pairs = [('AstraFirst.inc', 'KerrKoopman.Shared'), ('AstraSecond.inc', 'KerrKoopman.Shared')]
        self.assertTrue(CHECK.duplicate_namespace_errors(pairs, set()))

    def test_verified_file_does_not_authorize_different_namespace(self):
        pairs = [('AstraFirst.inc', 'Other'), ('AstraSecond.inc', 'Other')]
        allowed = {(path, 'KerrKoopman.Shared') for path, _ in pairs}
        self.assertTrue(CHECK.duplicate_namespace_errors(pairs, allowed))

    def test_registered_proof_requires_descriptive_scope(self):
        self.write('tools/verify.py', 'supplemental_scopes = {}\n')
        self.assert_rejected('Missing descriptive scope')

    def test_baseline_hash_cannot_be_replaced_by_changed_working_hash(self):
        path = 'lean/Elastica.lean'
        self.write(path, '-- changed original\n')
        self.manifest['files'][0]['sha256'] = hashlib.sha256((self.root / path).read_bytes()).hexdigest()
        self.save_manifest()
        self.assert_rejected('Baseline source cannot be adapted')

    def test_baseline_entry_cannot_be_omitted(self):
        self.manifest['files'] = self.manifest['files'][1:]
        self.save_manifest()
        self.assert_rejected('Baseline provenance coverage mismatch')

    def test_imported_working_hash_requires_a_documented_adaptation(self):
        path = 'linear_input/lean_check/Proof.inc'
        self.write(path, '-- unexplained changed proof\n')
        self.manifest['files'][1]['sha256'] = hashlib.sha256((self.root / path).read_bytes()).hexdigest()
        self.save_manifest()
        self.assert_rejected('Byte-identical provenance is inconsistent')

    def test_duplicate_manifest_path_is_rejected(self):
        self.manifest['files'].append(dict(self.manifest['files'][0]))
        self.save_manifest()
        self.assert_rejected('Duplicate retained source path')

    def test_unresolved_construction_error_is_not_a_success(self):
        self.manifest['construction_errors'] = ['Original source mismatch']
        self.save_manifest()
        self.assert_rejected('Unresolved manifest construction error')

    def test_multisource_adapter_requires_preserved_originals(self):
        row = self.manifest['files'][1]
        row.update(original_sha256=None, byte_identical=False, role='explicit_source_adapter',
                   permitted_adaptations=['Combine original source fragments.'],
                   source_files=[{'preserved_copy': 'sources/missing.inc', 'original_sha256': 'b' * 64}])
        self.save_manifest()
        self.assert_rejected('Adapter original is not preserved')

    def test_documented_single_source_adapter_preserves_original_hash(self):
        row = self.manifest['files'][1]
        original_digest = row['original_sha256']
        path = row['path']
        self.write(path, '-- documented formatting adapter\n')
        row.update(sha256=hashlib.sha256((self.root / path).read_bytes()).hexdigest(),
                   byte_identical=False, role='adapted_retained_source',
                   permitted_adaptations=['Documented formatting change; original digest retained.'])
        self.save_manifest()
        result = CHECK.audit(self.root)
        self.assertTrue(result['passed'], result)
        self.assertEqual(row['original_sha256'], original_digest)
        self.assertNotEqual(row['sha256'], original_digest)

    def test_documented_multisource_adapter_with_preserved_original_passes(self):
        source = 'sources/original.inc'
        self.write(source, '-- original standalone source\n')
        original = self.row(source, 'preserved_unmodified_original')
        self.manifest['files'].append(original)
        self.manifest['files'][1].update(
            original_sha256=None, byte_identical=False, role='explicit_source_adapter',
            permitted_adaptations=['Remove standalone import for the joint assembly.'],
            source_files=[{'preserved_copy': source, 'original_sha256': original['sha256']}])
        self.save_manifest()
        result = CHECK.audit(self.root)
        self.assertTrue(result['passed'], result)


if __name__ == '__main__':
    unittest.main()
