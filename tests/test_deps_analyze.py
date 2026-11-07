"""Unit tests for the kernel dependency analysis rules (synthetic data, no Lean)."""
import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("deps_analyze", ROOT / "tools/deps/analyze.py")
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)


def decl(name, kind="theorem", module="PrimitiveMain", line=1, internal=False, tc=(), vc=(), head=None):
    return dict(name=name, kind=kind, module=module, line=line, internal=internal,
                type_consts=list(tc), value_consts=list(vc),
                head=dict(const=head, args=2) if head else None)


SPANS = [(1, 100, "initial", "linear_input/lean_check/Design.lean"),
         (101, 200, "subsequent", "linear_input/lean_check/A.inc"),
         (201, 300, "subsequent", "linear_input/lean_check/B.inc")]


def run(decls, external=()):
    raw = dict(declarations=decls, external=list(external), module_imports=[])
    g = A.build(raw, SPANS, {})
    return g, A.analyze(g)


class DepsAnalyzeTests(unittest.TestCase):
    def test_own_auxiliary_is_inlined_and_foreign_auxiliary_maps_to_owner(self):
        decls = [
            decl("Init.base", kind="def", line=10),
            decl("Init.lemma", line=20, tc=["Init.base"]),
            decl("A.f", kind="def", line=110),
            decl("A.f.eq_1", line=None, tc=["A.f"]),
            decl("A.thm", line=120, vc=["A.thm._proof_1", "A.f.eq_1"]),
            decl("A.thm._proof_1", line=None, internal=True, vc=["Init.lemma"]),
        ]
        g, rows = run(decls)
        self.assertNotIn("A.thm._proof_1", rows)
        self.assertEqual(rows["A.thm"]["direct"]["proof"], ["A.f", "Init.lemma"])
        self.assertEqual(rows["A.thm"]["hops_to_initial_proof_only"], 1)

    def test_private_auxiliary_resolves_to_private_owner(self):
        p = "_private.Elastica.X.0."
        decls = [decl(p + "Elastica.helper", module="Elastica.X", line=5),
                 decl(p + "Elastica.helper._proof_1", module="Elastica.X", line=None, internal=True)]
        g, rows = run(decls)
        self.assertEqual(set(rows), {p + "Elastica.helper"})

    def test_application_of_earlier_theorem_allows_local_arguments_only(self):
        decls = [
            decl("A.general", line=110),
            decl("B.local", line=210),
            decl("B.inst", line=220, vc=["A.general", "B.local"], head="A.general"),
            decl("B.other", line=230, vc=["A.general", "Init.lemma"], head="A.general"),
            decl("Init.lemma", line=20),
        ]
        g, rows = run(decls)
        self.assertEqual(rows["B.inst"]["proof_shape"], "application_of_earlier_theorem")
        self.assertEqual(rows["B.other"]["proof_shape"], "composite")

    def test_missing_path_is_reported_as_none_not_false_claim(self):
        decls = [decl("B.island", line=210, vc=["Nat.succ"])]
        ext = [dict(name="Nat.succ", module="Init.Prelude", kind="ctor")]
        g, rows = run(decls, ext)
        r = rows["B.island"]
        self.assertFalse(r["reaches_initial_any_edge"])
        self.assertIsNone(r["hops_to_initial_any_edge"])
        self.assertEqual(r["direct_external_counts"]["proof"], {"core": 1})
        self.assertEqual(r["proof_shape"], "library_only")


class SharedProofTests(unittest.TestCase):
    def test_foreign_shared_proof_is_expanded_not_attributed(self):
        decls = [
            decl("Init.f", kind="def", line=10),
            decl("Init.f._proof_1", line=None, internal=True, vc=["Nat.succ"]),
            decl("A.g", kind="def", line=110, vc=["Init.f._proof_1"]),
            decl("A.h", kind="def", line=120, vc=["Init.f.eq_1"]),
            decl("Init.f.eq_1", line=None, tc=["Init.f"]),
        ]
        ext = [dict(name="Nat.succ", module="Init.Prelude", kind="ctor")]
        g, rows = run(decls, ext)
        self.assertEqual(rows["A.g"]["direct"]["definition"], [])
        self.assertEqual(rows["A.g"]["direct_external_counts"]["definition"], {"core": 1})
        self.assertEqual(rows["A.h"]["direct"]["definition"], ["Init.f"])


if __name__ == "__main__":
    unittest.main()
