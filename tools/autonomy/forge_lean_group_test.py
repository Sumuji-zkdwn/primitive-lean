"""PR-only regression: exact finite stages, then two new kernel certificates."""
import argparse
from pathlib import Path
from tools.autonomy import forge_lean_evolution as evo
from tools.autonomy import forge_lean_group as group
from tools.autonomy import forge_lean_feedback as fb
from tools.autonomy import forge_lean_reentry as reentry
from tools.autonomy import semantic_forge as sf
from tools.autonomy import forge_lean_certificate as cert


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--output", required=True, type=Path)
    p.add_argument("--finite-only", action="store_true")
    a = p.parse_args()
    seed_rank = min(
        ((-len(set(v)), r, v) for r in fb.recipes()
         if (v := [fb.reference(r, x) for x in range(256)])
         and len(set(v)) > 4 and any(v[x] not in cert.CONSTANTS for x in cert.CONSTANTS)),
        key=lambda row: row[:2])
    seed_perm = min(
        ((-sum(x != y for x, y in enumerate(v)), r, v) for r in reentry.recipes()
         if (v := [reentry.reference(r, x) for x in range(256)])
         and any(v[x] not in cert.CONSTANTS for x in cert.CONSTANTS)),
        key=lambda row: row[:2])
    assert evo.fingerprint(seed_rank[2]) == evo.OLD_SEED
    for r, v in [(seed_rank[1], seed_rank[2])]:
        assert v == [fb.packed(r, x) for x in range(256)]
    assert seed_perm[2] == [reentry.packed(seed_perm[1], x) for x in range(256)]
    tables = evo.roots(sf.read(evo.FIXTURE), 1,
                       {"seed:rank": seed_rank[2], "seed:reversible": seed_perm[2]})
    for generation in range(1, 5):
        selected, _, _ = evo.search(tables)
        recipe, values, invariant, pair = selected
        assert invariant["kind"] in ("unary", "diff")
        if generation == 1:
            assert evo.fingerprint(values) == "57102fa2e27f8fbc2662fad66483ec9038d18be1517d96a19834c396d9d2c0dd"
            symbol = "e:2490493c4dd3f5679212242d2"
        else:
            symbol = f"e:sim-{generation}"
        tables[symbol] = values
    assert not list(evo.components(tables))
    assert all(group.affine_witness(v) is None for v in tables.values() if len(set(v)) == 256)
    for kind in group.KINDS:
        selected, _, report = evo.search(tables)
        recipe, values, invariant, pair = selected
        assert invariant["kind"] == kind, (kind, invariant)
        assert report["group_extension"]["separating"] > 0
        assert group.witness(values, kind) == pair
        assert values == evo.evaluate(recipe, tables, independent=True)
        if kind == "affine":
            assert values == [x ^ int((x & 6) == 6) for x in range(256)]
        else:
            assert len(group.swaps(values)) % 2 == 1
        out = a.output / kind
        sha = evo.certificate(tables, values, invariant, pair, out)
        # Independent generation from exact same snapshot must be byte-identical.
        again = a.output / (kind + "-replay")
        assert evo.certificate(tables, values, invariant, pair, again) == sha
        assert (again / "Certificate.lean").read_bytes() == (out / "Certificate.lean").read_bytes()
        if not a.finite_only:
            evo.check_lean(out)
        try:
            evo.certificate(tables, values, invariant, [999], a.output / "bad")
        except ValueError:
            pass
        else:
            raise AssertionError("corrupted witness accepted")
        tables["e:extension-" + kind] = values
        print("PASS", kind, recipe, evo.fingerprint(values), pair, flush=True)
    assert evo.search(tables)[0] is None
    print("PASS both group extensions; no unsupported full-group claim", flush=True)


if __name__ == "__main__":
    main()
