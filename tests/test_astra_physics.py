"""Reject hidden proof rewrites and broken dependency/registration contracts."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('check_astra_physics', ROOT / 'tools/check_astra_physics.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class AstraSourceAudit(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.manifest = json.loads((ROOT / CHECK.MANIFEST).read_text('utf-8'))
        paths = {CHECK.MANIFEST, 'tools/verify_main_result.py', self.manifest['bridge_contract']['preserved_copy']}
        for row in self.manifest['modules']:
            paths.add(row['preserved_copy'])
            if 'destination' in row: paths.add(row['destination'])
        for path in paths:
            dest = self.root / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, dest)

    def save(self):
        (self.root / CHECK.MANIFEST).write_text(json.dumps(self.manifest), 'utf-8')

    def reject(self, message):
        result = CHECK.audit(self.root)
        self.assertFalse(result['passed'], result)
        self.assertTrue(any(message in error for error in result['errors']), result)

    def test_actual_selected_closure_passes(self):
        result = CHECK.audit(self.root)
        self.assertTrue(result['passed'], result)
        self.assertEqual(result['counts']['new_theorems'], 126)
        self.assertEqual(result['counts']['reused_original_theorems'], 29)
        self.assertEqual(result['bridge_direct_references'], 12)
        self.assertFalse(result['proof_edges_checked'])

    def test_rehashed_adapter_cannot_rewrite_proof_body(self):
        row = self.manifest['modules'][0]
        path = self.root / row['destination']
        path.write_bytes(path.read_bytes() + b'\n-- hidden modification\n')
        row['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.save()
        self.reject('beyond import removal')

    def test_removed_source_dependency_is_rejected(self):
        self.manifest['modules'] = [r for r in self.manifest['modules'] if r['module'] != 'KerrKoopman.PrimitiveSource']
        self.save()
        self.reject('Missing source dependency')

    def test_rehashed_reused_primitive_cannot_change(self):
        row = next(r for r in self.manifest['modules'] if r['role'] == 'reuse_existing')
        path = self.root / row['destination']
        path.write_bytes(path.read_bytes() + b'\n-- hidden modification\n')
        row['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.save()
        self.reject('beyond line endings')

    def test_reused_primitive_line_ending_equivalence_is_permitted(self):
        row = next(r for r in self.manifest['modules'] if r['role'] == 'reuse_existing')
        path = self.root / row['destination']
        path.write_bytes(path.read_bytes().replace(b'\r\n', b'\n').replace(b'\n', b'\r\n'))
        row['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.save()
        self.assertTrue(CHECK.audit(self.root)['passed'])

    def test_missing_additive_import_is_rejected(self):
        path = self.root / 'tools/verify_main_result.py'
        path.write_text(path.read_text('utf-8').replace('    "Mathlib.Analysis.SpecialFunctions.Arsinh",\n', ''), 'utf-8')
        self.reject('Missing additive Mathlib import')

    def test_incorrect_namespace_registration_is_rejected(self):
        path = self.root / 'tools/verify_main_result.py'
        path.write_text(path.read_text('utf-8').replace("'KerrKoopman.Riccati'", "'Wrong.Riccati'"), 'utf-8')
        self.reject('namespace registration mismatch')

    def test_wrong_dependency_order_is_rejected_even_if_manifest_agrees(self):
        first = self.manifest['modules'][0]
        constitutive = next(r for r in self.manifest['modules'] if r['module'] == 'KerrKoopman.PrimitiveConstitutive')
        i = self.manifest['modules'].index(constitutive)
        self.manifest['modules'][0], self.manifest['modules'][i] = constitutive, first
        self.save()
        path = self.root / 'tools/verify_main_result.py'
        text = path.read_text('utf-8')
        a = f"    ('{first['destination']}', '{first['namespace']}'),"
        b = f"    ('{constitutive['destination']}', '{constitutive['namespace']}'),"
        path.write_text(text.replace(a, 'REPLACE_ORDER').replace(b, a).replace('REPLACE_ORDER', b), 'utf-8')
        self.reject('dependency appears after dependent')

    def test_source_hash_change_is_rejected(self):
        row = self.manifest['modules'][0]
        path = self.root / row['preserved_copy']
        path.write_bytes(path.read_bytes() + b'\n')
        self.reject('Preserved source hash mismatch')

    def test_paths_cannot_escape_repository(self):
        self.manifest['modules'][0]['preserved_copy'] = '../outside.lean'
        self.save()
        self.reject('escapes repository')

    def test_contract_missing_declaration_is_rejected_after_rehash(self):
        row = self.manifest['bridge_contract']; path = self.root / row['preserved_copy']
        contract = json.loads(path.read_text('utf-8'))
        node = next(iter(contract['required_proof_edges']))
        contract['required_proof_edges'][node][0] = 'Missing.Theorem'
        path.write_text(json.dumps(contract), 'utf-8')
        row['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        self.save()
        self.reject('references missing declaration')

    def test_comments_cannot_forge_declaration_counts(self):
        text = '/- theorem bogus : False := by\n /- nested -/ -/\nnamespace Test\ntheorem real : True := True.intro\nend Test\n'
        self.assertEqual(CHECK.declarations(text, 'Test'), [('theorem', 'Test.real')])

    def test_all_direct_proof_edges_are_required(self):
        lines = [f'ASTRA_PROOF_EDGE|{source}|{target}|present'
                 for source, target in CHECK.proof_contract(self.root)]
        self.assertTrue(CHECK.audit_proof_edges(self.root, '\n'.join(lines))['passed'])
        missing = CHECK.audit_proof_edges(self.root, '\n'.join(lines[1:]))
        self.assertFalse(missing['passed'])
        self.assertEqual(len(missing['missing']), 1)

    def test_duplicate_direct_edge_evidence_is_rejected(self):
        lines = [f'ASTRA_PROOF_EDGE|{source}|{target}|present'
                 for source, target in CHECK.proof_contract(self.root)]
        report = CHECK.audit_proof_edges(self.root, '\n'.join(lines + lines[:1]))
        self.assertFalse(report['passed'])
        self.assertTrue(report['duplicate_results'])


if __name__ == '__main__':
    unittest.main()
