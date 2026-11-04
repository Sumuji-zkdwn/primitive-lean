"""Catalog discovery must not silently fall back to three example games."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("demo_catalog", Path(__file__).resolve().parents[1] / "catalog.py")
catalog = importlib.util.module_from_spec(spec)
spec.loader.exec_module(catalog)


class CatalogSelectionTests(unittest.TestCase):
    def test_all_keeps_non_example_environments(self):
        ids = ["wa30-deadbeef", "ls20-9607627b", "ar25-0c556536"]
        self.assertEqual(catalog.select_games(ids), sorted(ids))

    def test_prefix_resolves_one_exact_version(self):
        self.assertEqual(catalog.select_games(["ar25-0c556536", "wa30-deadbeef"], "wa30"), ["wa30-deadbeef"])

    def test_missing_catalog_never_falls_back_to_examples(self):
        with self.assertRaises(ValueError):
            catalog.select_games([])

    def test_ambiguous_version_requires_an_explicit_id(self):
        ids = ["ar25-deadbeef", "ar25-cafebabe"]
        with self.assertRaises(ValueError):
            catalog.select_games(ids, "ar25")

    def test_unknown_or_duplicate_explicit_selection_is_rejected(self):
        for selection in ("ls20", "ar25 ar25", "ar25 ar25-deadbeef"):
            with self.subTest(selection=selection), self.assertRaises(ValueError):
                catalog.select_games(["ar25-deadbeef"], selection)


if __name__ == "__main__":
    unittest.main()
