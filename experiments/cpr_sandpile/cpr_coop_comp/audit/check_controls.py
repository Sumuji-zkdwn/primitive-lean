"""Independently check control aggregation and all seven permutation p values.

Reads saved control results; does not rerun spatial simulations or import the
root comparison implementation. No participant identifiers are read here.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations
import csv
import hashlib
import json
import math

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent


def rows(path):
    with path.open(encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def main():
    conditions = {r["subject"]: r["condition"] for r in rows(ROOT / "cpr_empirical/conditions.csv") if r["group"] == "two"}
    prefix_path = ROOT / "cpr_coop_comp/controls/prefix90_trials.csv"
    spatial_path = ROOT / "cpr_coop_comp/controls/spatial99_trials.csv"
    prefix = {r["trial"]: r for r in rows(prefix_path)}
    spatial = {r["trial"]: r for r in rows(spatial_path)}
    assert len(prefix) == len(spatial) == 157 and prefix.keys() == spatial.keys()
    group_values = defaultdict(list)
    for trial, pr in prefix.items():
        sp = spatial[trial]
        subject = pr["subject"]
        assert sp["subject"] == subject
        assert pr["condition"] == sp["condition"] == conditions[subject]
        assert int(pr["prefix_harvests"]) == 90 and int(pr["total_harvests"]) >= 94
        assert int(sp["shuffles"]) == 99
        assert int(pr["u_total"]) - 90 == int(pr["v_total"])
        K = int(sp["harvest_count"])
        # Derive excess anew rather than taking the already-derived difference.
        excess = (float(sp["actual_v_total"]) - float(sp["shuffle_mean_v_total"])) / K
        assert abs(excess - float(sp["v_per_harvest_minus_shuffle_mean"])) < 1e-12
        group_values[subject].append((int(pr["v_total"]), excess))

    prior = rows(OUT / "pair_metrics.csv")
    assert [r["subject"] for r in prior] == sorted(conditions)
    metric_names = ["K", "v", "v_per_K", "cascade_fraction", "max_event_area_u", "prefix90_v", "placement_excess_v_per_K"]
    values = []
    for r in prior:
        pairs = group_values[r["subject"]]
        assert len(pairs) == int(r["n_rounds"])
        values.append([float(r[k]) for k in metric_names[:5]] + [math.fsum(v[j] for v in pairs) / len(pairs) for j in range(2)])
    values = np.asarray(values)
    is_coop = np.array([conditions[r["subject"]] == "Coop" for r in prior])
    assert int(is_coop.sum()) == 10 and len(values) == 20
    comp_mean, coop_mean = values[~is_coop].mean(axis=0), values[is_coop].mean(axis=0)
    observed = coop_mean - comp_mean
    # All balanced assignments. Independent direct enumeration in small batches.
    extreme = np.zeros(7, dtype=np.int64)
    count = 0
    batch = []
    total_sum = values.sum(axis=0)
    tolerance = 1e-12 * np.maximum(1., np.abs(observed))
    for assignment in combinations(range(20), 10):
        batch.append(assignment)
        if len(batch) == 2048:
            s = values[np.asarray(batch)].sum(axis=1)
            d = (2 * s - total_sum) / 10
            extreme += (np.abs(d) >= np.abs(observed) - tolerance).sum(axis=0)
            count += len(batch)
            batch = []
    if batch:
        s = values[np.asarray(batch)].sum(axis=1)
        d = (2 * s - total_sum) / 10
        extreme += (np.abs(d) >= np.abs(observed) - tolerance).sum(axis=0)
        count += len(batch)
    assert count == math.comb(20, 10) == 184756
    ps = extreme / count
    rank_order = sorted(range(7), key=lambda j: ps[j])
    adjusted, previous = np.empty(7), 0.
    for rank, j in enumerate(rank_order):
        previous = max(previous, min(1., (7 - rank) * ps[j]))
        adjusted[j] = previous

    reference = json.loads((ROOT / "cpr_coop_comp/control_comparison.json").read_text())
    checked = []
    for i, r in enumerate(reference["results"], 5):
        assert r["metric"] == metric_names[i]
        assert abs(comp_mean[i] - r["Comp_mean"]) < 1e-12
        assert abs(coop_mean[i] - r["Coop_mean"]) < 1e-12
        assert abs(observed[i] - r["difference_Coop_minus_Comp"]) < 1e-12
        assert ps[i] == r["exact_permutation_p_reference"]
        assert adjusted[i] == r["holm_across_five_main_plus_two_controls_reference"]
        checked.append({"metric": metric_names[i], "Comp_mean": float(comp_mean[i]), "Coop_mean": float(coop_mean[i]),
                        "Coop_minus_Comp": float(observed[i]), "extreme_assignments": int(extreme[i]),
                        "exact_p_reference": float(ps[i]), "holm_seven_reference": float(adjusted[i]),
                        "root_aggregation_and_p_agree": True})
    for j, r in enumerate(reference["holm_seven"]):
        assert ps[j] == r["exact_permutation_p_reference"]
        assert adjusted[j] == r["holm_seven_reference"]
    result = {"status": "pass", "scope": "Reaggregated 157 saved trial outputs into 20 equally weighted pair averages. Checked two control point estimates, all seven exact p values and Holm adjustments. Spatial simulations and bootstrap confidence intervals were not rerun.",
              "assignment_count": count, "controls": checked,
              "all_seven": [{"metric": name, "exact_p_reference": float(ps[j]), "holm_seven_reference": float(adjusted[j])} for j, name in enumerate(metric_names)],
              "interpretation": ["Permutation inference is reference-only, conditional on pair independence and label exchangeability.",
                                 "Prefix90 fixes input count, not elapsed time or harvesting opportunities.",
                                 "Placement excess compares the specified model against 99 location permutations of a round's fixed count histogram; it is not a behavioral causal adjustment."],
              "sources": [{"path": str(p.relative_to(ROOT)), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in (prefix_path, spatial_path, OUT / "pair_metrics.csv")]}
    (OUT / "control_comparison_check.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "controls": checked, "all_seven": result["all_seven"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
