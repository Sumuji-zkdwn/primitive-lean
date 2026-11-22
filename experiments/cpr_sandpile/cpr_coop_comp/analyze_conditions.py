"""Coop/Comp comparison on dyad means, using the previously verified CPR/ASM data."""
from pathlib import Path
import csv
import hashlib
import itertools
import json

import numpy as np


ROOT = Path(__file__).resolve().parent.parent
OUT = Path(__file__).resolve().parent
SEED = 20261121
BOOTSTRAPS = 100000
CORE = ["harvest_count", "extra_topplings", "extra_per_harvest", "cascade_fraction", "max_avalanche_area"]
CONTEXT = ["resource_persistence_240", "not_depleted_at_240", "balance_births", "terminal_tokens"]


def read_csv(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path, rows):
    with path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


def dyad_means(rows, metrics):
    result = []
    for subject in sorted({r["subject"] for r in rows}):
        group = [r for r in rows if r["subject"] == subject]
        conditions = {r["condition"] for r in group}
        assert len(conditions) == 1
        result.append({"subject": subject, "condition": conditions.pop(), "rounds": len(group),
                       **{m: float(np.mean([r[m] for r in group])) for m in metrics}})
    return result


def descriptive(rows, metrics):
    by_condition = {}
    for condition in ["Comp", "Coop"]:
        selected = [r for r in rows if r["condition"] == condition]
        by_condition[condition] = {"dyads": len(selected), "metrics": {
            m: {"mean": float(np.mean([r[m] for r in selected])),
                "median": float(np.median([r[m] for r in selected])),
                "minimum": float(min(r[m] for r in selected)),
                "maximum": float(max(r[m] for r in selected))}
            for m in metrics}}
    return by_condition


def compare(rows):
    subjects = [r["subject"] for r in rows]
    matrix = np.array([[r[m] for m in CORE] for r in rows], float)
    labels = np.array([r["condition"] == "Coop" for r in rows])
    assert labels.sum() == 10 and (~labels).sum() == 10
    coop, comp = matrix[labels], matrix[~labels]
    delta = coop.mean(axis=0) - comp.mean(axis=0)
    assignments = np.array(list(itertools.combinations(range(20), 10)), dtype=np.int16)
    selected_sums = matrix[assignments].sum(axis=1)
    permutation_delta = selected_sums / 10 - (matrix.sum(axis=0) - selected_sums) / 10
    p = np.mean(np.abs(permutation_delta) >= np.abs(delta)[None, :] - 1e-11, axis=0)
    rng = np.random.default_rng(SEED)
    ic = rng.integers(0, 10, size=(BOOTSTRAPS, 10))
    im = rng.integers(0, 10, size=(BOOTSTRAPS, 10))
    bootstrap_delta = coop[ic].mean(axis=1) - comp[im].mean(axis=1)
    bounds = np.quantile(bootstrap_delta, [.025, .975], axis=0)
    order = np.argsort(p)
    adjusted = np.empty(len(CORE))
    adjusted[order] = np.minimum(1., np.maximum.accumulate(p[order] * np.arange(len(CORE), 0, -1)))
    result = []
    for i, m in enumerate(CORE):
        result.append({"metric": m, "Comp_mean": float(comp[:, i].mean()), "Coop_mean": float(coop[:, i].mean()),
                       "difference_Coop_minus_Comp": float(delta[i]),
                       "ratio_of_condition_means": float(coop[:, i].mean() / comp[:, i].mean()),
                       "difference_ci95_low_dyad_bootstrap": float(bounds[0, i]),
                       "difference_ci95_high_dyad_bootstrap": float(bounds[1, i]),
                       "two_sided_exact_permutation_p": float(p[i]), "holm_p_five_metrics": float(adjusted[i]),
                       "n_dyads_Coop": 10, "n_dyads_Comp": 10})
    return result, {"seed": SEED, "bootstrap_draws": BOOTSTRAPS, "exact_assignments": len(assignments),
                    "dyad_order": subjects, "permutation_statistic": "Absolute difference in condition means; all choose(20,10) labels including the observed assignment",
                    "bootstrap": "Percentile interval for difference; resample dyads within each condition; assumes dyads independent",
                    "inference_scope": "Exploratory, not preregistered; five metric family uses Holm adjustment. Assignment randomization is unverified. Reused participant initials do not establish reused people; separate sensitivity groups matching initials."}


def main():
    OUT.mkdir(exist_ok=True)
    asm_path = ROOT / "cpr_redefinition/harvest_asm/summary.csv"
    raw_path = ROOT / "cpr_empirical/results/round_sand.csv"
    asm = [r for r in read_csv(asm_path) if r["group"] == "two" and r["drive_grains"] == "8"]
    raw = {r["trial"]: r for r in read_csv(raw_path)}
    rows = []
    for a in asm:
        r = raw[a["trial"]]
        k = int(a["harvest_count"])
        u = int(a["total_topplings"])
        assert k == int(r["harvest_window"]) and r["condition"] == a["condition"]
        assert r["qc"] != "exclude" and int(r["N_start"]) == 90
        duration = float(r["t_end"]) - float(r["t_start"])
        assert duration >= 240
        first_zero = float(r["first_zero"]) if r["first_zero"] not in ("", "nan", "None") else float("inf")
        elapsed_zero = first_zero - float(r["t_start"])
        rows.append({"trial": a["trial"], "subject": a["subject"], "condition": a["condition"],
                     "round": int(a["round"]), "qc": r["qc"],
                     "harvest_count": k, "extra_topplings": u-k,
                     "extra_per_harvest": (u-k)/k, "cascade_fraction": int(a["nonlocal_avalanche_count"])/k,
                     "max_avalanche_area": int(a["max_avalanche_area"]),
                     "resource_persistence_240": min(240., elapsed_zero),
                     "not_depleted_at_240": int(elapsed_zero >= 240),
                     "balance_births": int(r["balance_births"]), "terminal_tokens": int(r["N_end"]),
                     "observed_duration": duration})
    assert len(rows) == 157 and len({r["trial"] for r in rows}) == 157
    metrics = CORE + CONTEXT
    subjects = dyad_means(rows, metrics)
    assert len(subjects) == 20
    results, methods = compare(subjects)
    write_csv(OUT / "round_metrics.csv", rows)
    write_csv(OUT / "dyad_metrics.csv", subjects)
    write_csv(OUT / "condition_comparison.csv", results)

    sensitivity = {}
    selections = {
        "main_all_valid": rows,
        "exclude_review_rounds": [r for r in rows if not (r["subject"] == "20" and r["round"] in (1, 2))],
        "rounds_1_to_6_balanced": [r for r in rows if r["round"] <= 6],
        "rounds_3_to_6_balanced": [r for r in rows if 3 <= r["round"] <= 6],
    }
    for name, subset in selections.items():
        sensitivity[name] = {"rounds": len(subset), "summary": descriptive(dyad_means(subset, metrics), metrics)}
    by_round = []
    for number in range(1, 9):
        for condition in ["Comp", "Coop"]:
            subset = [r for r in rows if r["round"] == number and r["condition"] == condition]
            by_round.append({"round": number, "condition": condition, "dyads": len(subset),
                             **{m: float(np.mean([r[m] for r in subset])) for m in metrics}})
    write_csv(OUT / "by_round.csv", by_round)
    metadata = {"question": "Do Coop and Comp differ in the empirically driven sandpile?", "main_rounds": 157,
                "condition_rounds": {c: sum(r["condition"] == c for r in rows) for c in ["Comp", "Coop"]},
                "design": "Between-dyad conditions,10 dyads per condition, repeated rounds; participant independence unverified from initials",
                "weighting": "Calculate round metric, average rounds within each dyad, then give each dyad equal weight. Ratio metrics are average round ratios, not pooled event rates.",
                "metric_definitions": {
                    "harvest_count": "Successful logged harvests in [first TokenField,last TokenField), per round",
                    "extra_topplings": "Model u minus actual harvest K; direct-neighbor-drive cascade topplings v",
                    "extra_per_harvest": "v/K within each round, then equal round and dyad weighting",
                    "cascade_fraction": "Events with u>1 divided by harvest count within each round; same as nonlocal area>1",
                    "max_avalanche_area": "Largest event area with delta_u>0, including initial source distribution.1 means no cascade in the round.",
                    "resource_persistence_240": "min(first recorded zero-token timestamp minus first recorded field timestamp,240); if never depleted then240; all observation windows>=240sec",
                    "not_depleted_at_240": "No recorded zero before first field timestamp+240seconds",
                    "balance_births": "Births reconstructed by token balance N_end-N_start+harvest; not exact observed birth times",
                    "terminal_tokens": "Observed token count at final field record"
                }, "descriptive": descriptive(subjects, metrics), "comparison": results, "methods": methods,
                "sensitivity": sensitivity,
                "sources": [{"path": str(p.relative_to(ROOT)), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                            for p in [asm_path, raw_path, ROOT/"cpr_empirical/conditions.csv", ROOT/"cpr_empirical/quality_flags.csv"]]}
    (OUT / "comparison.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"comparison": results, "context": {c: metadata['descriptive'][c]['metrics']['resource_persistence_240'] for c in ['Comp','Coop']},
                      "sensitivity_means": {n: {c: {m: x['summary'][c]['metrics'][m]['mean'] for m in ['harvest_count','extra_per_harvest']} for c in ['Comp','Coop']} for n,x in sensitivity.items()}}, indent=2))


if __name__ == "__main__":
    main()
