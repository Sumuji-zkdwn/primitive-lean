"""Dependency source attribution across the actual assembler's approved context."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


A = load('deps_line_map_analyzer', ROOT / 'tools/deps/analyze.py')
C = load('deps_line_map_assembler', ROOT / 'tools/check_astra_physics.py')


class AssemblyLineMapTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.before = 'linear_input/lean_check/Before.inc'
        self.flow = 'linear_input/lean_check/AstraHilbertFlow.inc'
        self.after = 'linear_input/lean_check/After.inc'
        self.sources = [self.before, self.flow, self.after]
        self.write('linear_input/lean_check/All.lean',
                   b'import Mathlib\n-- Source: Design.lean\ntheorem initial : True := True.intro\n')
        self.write(self.before, b'theorem before : True := True.intro\n')
        self.write(self.flow, b'namespace KerrKoopman.HilbertFlow\n'
                             b'theorem mapped : True := True.intro\nend KerrKoopman.HilbertFlow\n')
        # Mixed source line endings and a final line with no newline must remain exact.
        self.write(self.after, b'namespace After\r\ntheorem later : True := True.intro\r\nend After')
        self.write('tools/check_astra_physics.py', (ROOT / 'tools/check_astra_physics.py').read_bytes())
        self.contexts = [dict(source=self.flow, kind='hilbertflow_set_exports', reason='Regression fixture')]
        self.report = dict(supplemental_sources=self.sources, assembly_contexts=self.contexts)
        self.save_manifest()
        self.assembled = self.root / 'PrimitiveMain.lean'
        self.assemble()

    def write(self, name, data):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def save_manifest(self):
        self.write('docs/astra/manifest.json', json.dumps(dict(assembly_contexts=self.contexts)).encode())

    def assemble(self, wrapped=True):
        chunks = [(self.root / 'linear_input/lean_check/All.lean').read_bytes()]
        for source in self.sources:
            raw = (self.root / source).read_bytes()
            chunks.append(C.assembly_fragment(source, raw, self.contexts) if wrapped else raw)
        self.assembled.write_bytes(b'import Extra\n' + b'\n'.join(chunks) + b'\n\n-- audit commands\n')

    def line(self, token):
        raw = self.assembled.read_bytes()
        return raw[:raw.index(token)].count(b'\n') + 1

    def spans(self):
        return A.line_map(self.assembled, self.report, self.root)

    def reject(self, message):
        with self.assertRaisesRegex(ValueError, message):
            self.spans()

    def test_actual_wrapper_maps_only_original_source_lines(self):
        spans = self.spans()
        for token, source in [(b'theorem before', self.before), (b'theorem mapped', self.flow),
                              (b'theorem later', self.after), (b'end After', self.after)]:
            self.assertEqual(A.locate(spans, self.line(token)), ('subsequent', source))
        for token in [b'section\n', b'export Set', b'-- audit commands']:
            self.assertEqual(A.locate(spans, self.line(token)), (None, None))
        raw = self.assembled.read_bytes()
        flow_raw = (self.root / self.flow).read_bytes()
        end = raw.index(flow_raw) + len(flow_raw)
        suffix_blank = raw[:end].count(b'\n') + 1
        self.assertEqual(A.locate(spans, suffix_blank), (None, None))
        self.assertEqual(A.locate(spans, suffix_blank + 1), (None, None))  # wrapper end

    def test_following_source_has_exact_six_line_context_shift(self):
        wrapped_line = self.line(b'theorem later')
        self.assemble(wrapped=False)
        legacy_line = self.line(b'theorem later')
        self.assertEqual(wrapped_line - legacy_line, 6)

    def test_historical_report_without_context_metadata_stays_unwrapped(self):
        del self.report['assembly_contexts']
        self.assemble(wrapped=False)
        self.assertEqual(A.locate(self.spans(), self.line(b'theorem later')), ('subsequent', self.after))

    def test_historical_report_cannot_silently_accept_wrapped_bytes(self):
        del self.report['assembly_contexts']
        self.reject('assembly mismatch')

    def test_changed_prefix_is_rejected(self):
        self.assembled.write_bytes(self.assembled.read_bytes().replace(b'export Set', b'export Finset'))
        self.reject('assembly mismatch')

    def test_changed_suffix_is_rejected(self):
        self.assembled.write_bytes(self.assembled.read_bytes().replace(b'\nend\n', b'\nwrong\n'))
        self.reject('assembly mismatch')

    def test_changed_source_body_is_rejected(self):
        self.assembled.write_bytes(self.assembled.read_bytes().replace(b'theorem mapped', b'theorem edited'))
        self.reject('assembly mismatch')

    def test_non_newline_separator_is_rejected(self):
        self.assembled.write_bytes(self.assembled.read_bytes().replace(b'\n\n-- audit', b'X\n-- audit'))
        self.reject('separator mismatch')

    def test_report_and_manifest_must_agree(self):
        self.report['assembly_contexts'] = []
        self.reject('report/manifest mismatch')

    def test_unknown_context_is_rejected_even_if_metadata_agrees(self):
        self.contexts[0]['kind'] = 'arbitrary_code'
        self.save_manifest()
        self.reject('invalid assembly context')

    def test_duplicate_context_is_rejected(self):
        self.contexts.append(dict(self.contexts[0])); self.save_manifest()
        self.reject('Duplicate assembly context')

    def test_different_source_cannot_receive_the_context(self):
        self.contexts[0]['source'] = self.after; self.save_manifest()
        self.reject('invalid assembly context')

    def test_recorded_context_hash_must_match(self):
        self.report['source_hashes'] = {'docs/astra/manifest.json': '0' * 64}
        self.reject('context input hash mismatch')

    def test_unreported_context_target_is_rejected(self):
        self.report['supplemental_sources'] = [self.before, self.after]
        self.reject('context coverage mismatch')


class ScopedEOFLineMapTests(unittest.TestCase):
    write = AssemblyLineMapTests.write
    save_manifest = AssemblyLineMapTests.save_manifest
    assemble = AssemblyLineMapTests.assemble
    line = AssemblyLineMapTests.line
    spans = AssemblyLineMapTests.spans
    reject = AssemblyLineMapTests.reject

    def setUp(self):
        AssemblyLineMapTests.setUp(self)
        self.flow = 'linear_input/lean_check/AstraFourierProjection.inc'
        self.sources = [self.before, self.flow, self.after]
        self.write(self.flow, b'noncomputable section\r\nnamespace KerrKoopman.FourierProjection\r\n'
                             b'theorem scoped : True := True.intro\r\nend KerrKoopman.FourierProjection\r\n')
        self.contexts = [dict(source=self.flow, kind=C.ASSEMBLY_CONTEXTS[self.flow][0], reason='EOF section fixture')]
        self.report = dict(supplemental_sources=self.sources, assembly_contexts=self.contexts)
        self.save_manifest(); self.assemble()

    def test_eof_section_closures_are_not_source_lines(self):
        spans = self.spans(); assembled = self.assembled.read_bytes()
        source = (self.root / self.flow).read_bytes()
        start = assembled.index(source); stop = start + len(source)
        first = assembled[:start].count(b'\n') + 1
        last = first + len(source.splitlines()) - 1
        for line in range(first, last + 1):
            self.assertEqual(A.locate(spans, line), ('subsequent', self.flow))
        _, prefix, suffix = C.ASSEMBLY_CONTEXTS[self.flow]
        self.assertEqual(sum(line == b'end' for line in suffix.splitlines()), 2)
        for line in range(first - prefix.count(b'\n'), first):
            self.assertEqual(A.locate(spans, line), (None, None))
        for line in range(last + 1, last + 1 + suffix.count(b'\n')):
            self.assertEqual(A.locate(spans, line), (None, None))
        self.assertEqual(A.locate(spans, self.line(b'theorem later')), ('subsequent', self.after))

    def test_following_source_shift_includes_both_closures(self):
        wrapped = self.line(b'theorem later')
        self.assemble(wrapped=False)
        _, prefix, suffix = C.ASSEMBLY_CONTEXTS[self.flow]
        self.assertEqual(wrapped - self.line(b'theorem later'), prefix.count(b'\n') + suffix.count(b'\n'))

    def test_missing_eof_closure_is_rejected(self):
        text = self.assembled.read_bytes(); source = (self.root / self.flow).read_bytes()
        stop = text.index(source) + len(source)
        suffix = C.ASSEMBLY_CONTEXTS[self.flow][2]
        self.assembled.write_bytes(text[:stop] + suffix.replace(b'end\n', b'', 1) + text[stop + len(suffix):])
        self.reject('assembly mismatch')

    def test_mutated_scoped_prefix_is_rejected(self):
        _, prefix, _ = C.ASSEMBLY_CONTEXTS[self.flow]
        self.assembled.write_bytes(self.assembled.read_bytes().replace(prefix, prefix + b'open Finset\n', 1))
        self.reject('assembly mismatch')


if __name__ == '__main__':
    unittest.main()
