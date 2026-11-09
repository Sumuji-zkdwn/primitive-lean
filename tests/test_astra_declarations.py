"""Source-name coverage and generated-environment audit failure controls."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('astra_declaration_audit', ROOT / 'tools/check_astra_physics.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class SourceDeclarations(unittest.TestCase):
    def parse(self, body):
        return CHECK.source_declarations(body, 'Example', 'fixture.inc')

    def test_nested_namespace_sections_and_structure(self):
        source = ('noncomputable section\nnamespace Example\nstructure Input where\n  n : Nat\n'
                  'namespace Input\nsection Variables\n@[simp] theorem result : True := True.intro\n'
                  'end Variables\nend Input\nend Example\n')
        rows = self.parse(source)
        self.assertEqual([(d['name'], d['kind'], d['line']) for d in rows],
                         [('Example.Input', 'structure', 3), ('Example.Input.result', 'theorem', 7)])

    def test_named_instance_is_recorded_anonymous_instance_is_not(self):
        rows = self.parse('namespace Example\ninstance named : Inhabited Nat := inferInstance\n'
                          'instance : Inhabited Int := inferInstance\nend Example\n')
        self.assertEqual([(d['name'], d['kind']) for d in rows], [('Example.named', 'instance')])

    def test_comments_and_strings_preserve_header_line(self):
        rows = self.parse('namespace Example\n/- theorem fake : False := by\n/- nested -/ -/\n'
                          'def text := "theorem fake"\n-- theorem fake\ntheorem real : True := True.intro\nend Example\n')
        self.assertEqual([(d['name'], d['line']) for d in rows], [('Example.text', 4), ('Example.real', 6)])

    def test_private_cannot_be_misreported_as_public(self):
        for prefix in ('private ', 'noncomputable private ', '  private '):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, 'Private source'):
                self.parse('namespace Example\n' + prefix + 'def absolute := 1\nend Example\n')

    def test_unsupported_declaration_forms_are_rejected(self):
        for header in ('protected theorem x : True := True.intro', 'noncomputable protected def x := 1', 'opaque x : Nat',
                       'class X where', 'inductive X where', 'mutual', 'public def x := 1'):
            with self.subTest(header=header), self.assertRaisesRegex(ValueError, 'Unsupported source declaration'):
                self.parse('namespace Example\n' + header + '\nend Example\n')

    def test_indented_named_declaration_cannot_disappear(self):
        with self.assertRaisesRegex(ValueError, 'Unsupported indented'):
            self.parse('namespace Example\n  theorem hidden : True := True.intro\nend Example\n')

    def test_wrong_or_escaping_namespace_is_rejected(self):
        for source in ('namespace Other\nend Other\n',
                       'namespace Example\nend Example\ndef outside := 1\n',
                       'namespace Example\ndef _root_.outside := 1\nend Example\n'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.parse(source)

    def test_scope_mismatch_and_unclosed_namespace_are_rejected(self):
        for source in ('namespace Example\nend Other\n', 'end\n', 'namespace Example\n'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.parse(source)

    def test_duplicate_fully_qualified_name_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate source declaration'):
            self.parse('namespace Example\ndef a := 1\nend Example\nnamespace Example\ndef a := 2\nend Example\n')

    def test_unclosed_comment_cannot_hide_declaration(self):
        with self.assertRaisesRegex(ValueError, 'Unclosed Lean'):
            self.parse('namespace Example\n/- hidden\ntheorem x : False := by\nend Example\n')


class EnvironmentAudit(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(); self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        (self.root / 'docs/astra').mkdir(parents=True)
        (self.root / 'proof.inc').write_text('namespace Example\nstructure Input where\n  n : Nat\n'
            'instance named : Inhabited Nat := inferInstance\ntheorem result : True := True.intro\nend Example\n', encoding='utf-8')
        self.manifest = dict(modules=[dict(namespace='Example', destination='proof.inc')], native_bridges=[])
        self.save()
        self.records = [('Example.Input', 'inductive', ''), ('Example.Input.mk', 'constructor', ''),
                        ('Example.Input.rec', 'recursor', ''), ('Example.named', 'definition', ''),
                        ('Example.result', 'theorem', ''), ('_private.Assembly.0.Example.helper', 'definition', 'Classical.choice')]

    def save(self):
        (self.root / CHECK.MANIFEST).write_text(json.dumps(self.manifest), encoding='utf-8')

    def audit(self, records=None, total=None):
        rows = self.records if records is None else records
        log = '\n'.join('ASTRA_ENV|' + '|'.join(row) for row in rows)
        return CHECK.audit_environment(self.root, log + '\nASTRA_ENV_TOTAL|' + str(len(rows) if total is None else total))

    def test_generated_and_private_constants_are_audited_separately(self):
        result = self.audit()
        self.assertTrue(result['passed'], result)
        self.assertEqual(result['source_named_declarations'], 3)
        self.assertEqual(result['environment_declarations'], 6)

    def test_prop_valued_instance_is_a_kernel_theorem(self):
        self.records[3] = ('Example.named', 'theorem', '')
        result = self.audit()
        self.assertTrue(result['passed'], result)
        self.assertEqual(result['source_named_declarations'], 3)

    def test_instance_cannot_be_a_user_axiom_or_structure(self):
        for kind in ('axiom', 'inductive'):
            with self.subTest(kind=kind):
                self.records[3] = ('Example.named', kind, '')
                self.assertFalse(self.audit()['passed'])

    def test_forbidden_axiom_on_generated_helper_is_rejected(self):
        self.records[-1] = (self.records[-1][0], 'definition', 'sorryAx')
        self.assertFalse(self.audit()['passed'])

    def test_missing_explicit_structure_or_instance_is_rejected(self):
        for missing in ('Example.Input', 'Example.named'):
            with self.subTest(missing=missing):
                self.assertFalse(self.audit([r for r in self.records if r[0] != missing])['passed'])

    def test_wrong_source_kind_is_rejected(self):
        self.records[0] = ('Example.Input', 'definition', '')
        self.assertFalse(self.audit()['passed'])

    def test_duplicate_result_is_rejected(self):
        self.assertFalse(self.audit(self.records + [self.records[0]])['passed'])

    def test_missing_or_incorrect_total_is_rejected(self):
        self.assertFalse(CHECK.audit_environment(self.root, '')['passed'])
        self.assertFalse(self.audit(total=99)['passed'])

    def test_namespace_prefix_collision_is_rejected(self):
        self.assertFalse(self.audit(self.records + [('ExampleOther.fake', 'definition', '')])['passed'])

    def test_reused_source_names_require_coverage(self):
        (self.root / 'reused.inc').write_text('namespace Reused\ntheorem original : True := True.intro\nend Reused\n', encoding='utf-8')
        self.manifest['modules'].append(dict(namespace='Reused', destination='reused.inc', role='reuse_existing'))
        self.save()
        self.assertFalse(self.audit()['passed'])
        self.assertTrue(self.audit(self.records + [('Reused.original', 'theorem', '')])['passed'])

    def test_namespace_cannot_inject_lean_command(self):
        self.manifest['modules'][0]['namespace'] = 'Example\naxiom fake : False'
        self.save()
        with self.assertRaisesRegex(ValueError, 'Invalid Astra environment namespace'):
            CHECK.environment_audit_commands(self.root)


if __name__ == '__main__':
    unittest.main()
