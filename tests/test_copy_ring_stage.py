"""Regression tests for copy_ring_stage.classify (no Lean needed)."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location(
    'copy_ring_stage', Path(__file__).resolve().parents[1] / 'tools/deps/copy_ring_stage.py')
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)
STARTS = {0: 5, 1: 10}


class ClassifyTests(unittest.TestCase):
    def test_import_error_is_not_a_proof(self):
        log = "RingStage.lean:1:0: error: unknown module prefix 'Foo'\n"
        self.assertEqual(MOD.classify(log, 1, STARTS, 2), (['not_checked'] * 2, 'compile_failed'))

    def test_crash_without_located_error_is_not_a_proof(self):
        self.assertEqual(MOD.classify('', 137, STARTS, 2), (['not_checked'] * 2, 'compile_failed'))

    def test_error_inside_one_theorem(self):
        log = "RingStage.lean:12:2: error: ring failed\n"
        self.assertEqual(MOD.classify(log, 1, STARTS, 2), (['proved_equal', 'not_proved'], 'checked'))

    def test_clean_compile(self):
        self.assertEqual(MOD.classify('', 0, STARTS, 2), (['proved_equal', 'proved_equal'], 'checked'))


if __name__ == '__main__':
    unittest.main()
