"""Reject hidden proof rewrites and broken dependency/registration contracts."""
import hashlib
import importlib.util
import ast
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
        paths.update(row['destination'] for row in self.manifest.get('native_bridges', []))
        paths.update(CHECK.contract_path(row) for row in self.manifest.get('additional_bridge_contracts', []))
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
        self.assertEqual(result['counts'], self.manifest['counts'])
        self.assertEqual(result['counts']['reused_original_theorems'], 29)
        self.assertEqual(result['bridge_direct_references'], len(CHECK.proof_contract(self.root)))
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

    def native_fixture(self):
        """Use the real bridge when present, otherwise add a tiny ledger fixture."""
        if self.manifest.get('native_bridges'):
            return self.manifest['native_bridges'][0]
        destination = 'linear_input/lean_check/AstraNativeFixture.inc'
        raw = b'namespace AstraNativeFixture\ntheorem witness : True := True.intro\nend AstraNativeFixture\n'
        (self.root / destination).write_bytes(raw)
        contract_path = 'docs/astra/native_fixture_contract.json'
        contract = {'required_proof_edges': {'AstraNativeFixture.witness': ['KerrKoopman.HilbertFlow.exists_global']}}
        contract_raw = json.dumps(contract).encode()
        (self.root / contract_path).write_bytes(contract_raw)
        row = dict(module='AstraNativeFixture', namespace='AstraNativeFixture', destination=destination,
                   sha256=CHECK.sha(raw), original_sha256=CHECK.sha(raw), theorem_count=1, declaration_count=1,
                   role='repository_native_proof', origin='authored_in_primitive_lean',
                   authored_on_parent_commit='a' * 40, authorship_description='Native proof fixture; never an import adapter.',
                   dependencies=['KerrKoopman.HilbertFlow'], required_mathlib_imports=[], proof_contract=contract_path)
        self.manifest.update(schema_version=2, native_bridges=[row], additional_bridge_contracts=[dict(
            path=contract_path, sha256=CHECK.sha(contract_raw), theorem_nodes=1, direct_references=1)])
        counts = self.manifest['counts']
        counts.update(import_only_modules=counts['new_proof_modules'], import_only_theorems=counts['new_theorems'],
                      repository_native_modules=1, repository_native_theorems=1)
        for key in ('new_proof_modules', 'new_theorems', 'new_physics_theorems'): counts[key] += 1
        registry_path = self.root / 'tools/verify_main_result.py'
        text = registry_path.read_text('utf-8'); tree = ast.parse(text)
        node = next(n for n in ast.walk(tree) if isinstance(n, ast.Assign)
                    and any(isinstance(t, ast.Name) and t.id == 'SUPPLEMENTS' for t in n.targets))
        lines = text.splitlines(keepends=True)
        lines.insert(node.end_lineno - 1, f"    ('{destination}', 'AstraNativeFixture'),\n")
        registry_path.write_text(''.join(lines), 'utf-8')
        self.save()
        return row

    def test_explicit_native_proof_ledger_passes_source_audit(self):
        self.native_fixture()
        result = CHECK.audit(self.root)
        self.assertTrue(result['passed'], result)
        self.assertGreater(result['counts']['repository_native_theorems'], 0)

    def test_native_proof_cannot_pretend_import_only_origin(self):
        row = self.native_fixture(); row['origin'] = 'import_only_adapter'; self.save()
        self.reject('explicit repository authorship')

    def test_native_proof_rehash_does_not_replace_creation_hash(self):
        row = self.native_fixture(); path = self.root / row['destination']
        path.write_bytes(path.read_bytes() + b'\n-- changed body\n')
        row['sha256'] = CHECK.sha(path.read_bytes()); self.save()
        self.reject('creation hash mismatch')

    def test_native_proof_requires_dependency_closure(self):
        row = self.native_fixture(); row['dependencies'].append('KerrKoopman.Missing'); self.save()
        self.reject('Missing native bridge dependency')

    def test_native_proof_requires_registered_contract(self):
        row = self.native_fixture(); row['proof_contract'] = 'docs/astra/missing_contract.json'; self.save()
        self.reject('lacks registered proof contract')

    def test_native_proof_cannot_claim_preserved_import_adapter(self):
        row = self.native_fixture(); row['transformation'] = 'remove_import_lines_exact_bytes'; self.save()
        self.reject('cannot claim import-only adaptation')

    def test_assembly_context_preserves_exact_source_span(self):
        source = 'linear_input/lean_check/AstraHilbertFlow.inc'
        raw = (self.root / source).read_bytes()
        assembled = CHECK.assembly_fragment(source, raw, self.manifest['assembly_contexts'])
        prefix = (b'section\nnamespace KerrKoopman.HilbertFlow\n'
                  b'export Set (piecewise union_comm)\nend KerrKoopman.HilbertFlow\n')
        self.assertTrue(assembled.startswith(prefix))
        self.assertTrue(assembled.endswith(b'\nend\n'))
        self.assertEqual(assembled[len(prefix):-len(b'\nend\n')], raw)

    def test_assembly_context_does_not_rewrite_other_sources(self):
        row = self.manifest['modules'][0]
        raw = (self.root / row['destination']).read_bytes()
        self.assertEqual(CHECK.assembly_fragment(row['destination'], raw, self.manifest['assembly_contexts']), raw)

    def test_missing_required_assembly_context_is_rejected(self):
        self.manifest['assembly_contexts'] = []; self.save()
        self.reject('Assembly context coverage mismatch')

    def test_assembly_context_cannot_inject_arbitrary_lean(self):
        self.manifest['assembly_contexts'][0]['prefix'] = 'axiom fake : False\n'; self.save()
        self.reject('Unapproved assembly context')

    def test_unknown_assembly_context_is_rejected(self):
        self.manifest['assembly_contexts'][0]['kind'] = 'rewrite_proofs'; self.save()
        self.reject('Unapproved assembly context')

    def test_duplicate_assembly_context_is_rejected(self):
        self.manifest['assembly_contexts'].append(dict(self.manifest['assembly_contexts'][0])); self.save()
        self.reject('Duplicate assembly context')

    def test_assembly_context_cannot_target_another_proof(self):
        self.manifest['assembly_contexts'][0]['source'] = self.manifest['modules'][0]['destination']; self.save()
        self.reject('Unapproved assembly context')


if __name__ == '__main__':
    unittest.main()
