"""Independent pair-level Coop/Comp summaries and uncertainty analyses.

No root analysis functions are imported. Participant initials are read only to
construct an anonymous overlap sensitivity graph; no initials/names are saved.
"""
from pathlib import Path
from collections import Counter, defaultdict
from itertools import combinations, chain
from zipfile import ZipFile
import csv
import hashlib
import io
import json
import math
import re
import xml.etree.ElementTree as ET

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
B = 200000
SEED = 20261121
METRICS = ("K", "v", "v_per_K", "cascade_fraction", "max_event_area_u")


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def source_design(conditions):
    source = ROOT / "cpr_empirical_sources" / "02_expCPR_2player(1).zip"
    ns = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    with ZipFile(source) as outer:
        books = [n for n in outer.namelist() if "/03_rawdata/" in n and n.endswith(".xlsx")]
        require(len(books) == 1, "Ambiguous source condition workbook")
        content = outer.read(books[0])
    with ZipFile(io.BytesIO(content)) as z:
        shared = []
        if "xl/sharedStrings.xml" in z.namelist():
            shared = ["".join(t.text or "" for t in si.findall(".//m:t", ns))
                      for si in ET.fromstring(z.read("xl/sharedStrings.xml"))]
        raw = []
        for row in ET.fromstring(z.read("xl/worksheets/sheet1.xml")).find("m:sheetData", ns):
            record = {}
            for cell in row:
                value = cell.find("m:v", ns)
                value = value.text if value is not None else ""
                if cell.get("t") == "s":
                    value = shared[int(value)]
                elif cell.get("t") == "inlineStr":
                    value = "".join(t.text or "" for t in cell.findall(".//m:t", ns))
                record[re.sub(r"\d+", "", cell.get("r"))] = value
            if re.fullmatch(r"\d+", record.get("A", "")):
                raw.append(record)
    require(len(raw) == 20, "Unexpected number of original pair rows")
    label_pairs = defaultdict(set)
    label_occurrences = Counter()
    all_two_letter = True
    within_pair_same_label = 0
    for row in raw:
        subject = f"{int(row['A']):02d}"
        require(conditions[subject] == row["E"], "Condition export disagrees with XLSX")
        labels = [re.sub(r"\s+", "", row[col]).upper() for col in ("B", "C")]
        all_two_letter &= all(bool(re.fullmatch(r"[A-Z]{2}", label)) for label in labels)
        within_pair_same_label += int(labels[0] == labels[1])
        for label in labels:
            label_pairs[label].add(subject)
            label_occurrences[label] += 1
    edges = Counter()
    reused = []
    for label, pair_set in label_pairs.items():
        if len(pair_set) > 1:
            pair_ids = sorted(pair_set)
            reused.append({"pairs": pair_ids, "conditions": [conditions[s] for s in pair_ids],
                           "occurrences": label_occurrences[label]})
            edges.update(combinations(pair_ids, 2))
    reused.sort(key=lambda r: r["pairs"])
    for i, row in enumerate(reused, 1):
        row["anonymous_repeat_label"] = f"repeat_{i:02d}"
    graph = {subject: set() for subject in conditions}
    for left, right in edges:
        graph[left].add(right)
        graph[right].add(left)
    components, unseen = [], set(graph)
    while unseen:
        first = min(unseen)
        stack, component = [first], set()
        while stack:
            subject = stack.pop()
            if subject in component:
                continue
            component.add(subject)
            stack.extend(graph[subject] - component)
        unseen -= component
        components.append(sorted(component))
    overlapping = sorted(subject for subject, adjacent in graph.items() if adjacent)
    return {
        "condition_design": "between pair IDs: each pair has one fixed condition, no pair-ID crossover",
        "condition_table_and_original_xlsx_agree": True,
        "pair_count": 20, "condition_pair_counts": dict(Counter(conditions.values())),
        "participant_label_slots": sum(label_occurrences.values()),
        "distinct_initial_strings": len(label_occurrences),
        "all_original_labels_two_ascii_letters": bool(all_two_letter),
        "normalization_for_sensitivity_graph": "remove whitespace and uppercase; original strings are not output",
        "identity_status": "These are two-letter initial-like labels, not unique person identifiers. Reuse may mean the same person or an initials collision; number of actual people is unresolved.",
        "within_pair_same_initials_count": within_pair_same_label,
        "reused_initial_groups": reused,
        "overlap_edges": [{"pairs": list(edge), "shared_initial_strings": count} for edge, count in sorted(edges.items())],
        "connected_components_under_same_initials_same_person_assumption": components,
        "component_count": len(components), "pairs_touching_any_reused_initial": overlapping,
        "source_workbook_sha256": hashlib.sha256(content).hexdigest(),
        "causal_assignment_note": "One-condition-per-pair is verified. Random assignment and human independence are not established by these labels/tables.",
    }


def q95(values):
    return np.quantile(values, [.025, .975], axis=0).T


def pair_bootstrap(comp, coop):
    rng = np.random.default_rng(np.random.SeedSequence([SEED, 1]))
    c = comp[rng.integers(0, len(comp), size=(B, len(comp)))]
    p = coop[rng.integers(0, len(coop), size=(B, len(coop)))]
    cm, pm = c.mean(axis=1), p.mean(axis=1)
    cmed, pmed = np.median(c, axis=1), np.median(p, axis=1)
    return {"difference_mean": q95(pm - cm), "Comp_mean": q95(cm), "Coop_mean": q95(pm),
            "difference_median": q95(pmed - cmed), "Comp_median": q95(cmed), "Coop_median": q95(pmed)}


def component_bootstrap(values, pair_ids, conditions, components):
    ncomponents = len(components)
    pos = {subject: i for i, subject in enumerate(pair_ids)}
    sums = np.zeros((ncomponents, 2, values.shape[1]))
    counts = np.zeros((ncomponents, 2), dtype=int)
    for ci, component in enumerate(components):
        for subject in component:
            gi = 0 if conditions[subject] == "Comp" else 1
            sums[ci, gi] += values[pos[subject]]
            counts[ci, gi] += 1
    rng = np.random.default_rng(np.random.SeedSequence([SEED, 2]))
    differences, group_means, denominators = [], [], []
    completed = rejected = 0
    while completed < B:
        batch = min(8192, B - completed)
        indices = rng.integers(0, ncomponents, size=(batch, ncomponents))
        nn = counts[indices].sum(axis=1)
        ss = sums[indices].sum(axis=1)
        valid = np.all(nn > 0, axis=1)
        rejected += int((~valid).sum())
        means = ss[valid] / nn[valid, :, None]
        differences.append(means[:, 1] - means[:, 0])
        group_means.append(means)
        denominators.append(nn[valid])
        completed += int(valid.sum())
    diff = np.concatenate(differences)
    means = np.concatenate(group_means)
    nn = np.concatenate(denominators)
    return {"difference_mean": q95(diff), "Comp_mean": q95(means[:, 0]), "Coop_mean": q95(means[:, 1]),
            "components": ncomponents, "valid_resamples": len(diff), "rejected_empty_condition_resamples": rejected,
            "resampled_pair_count_range": {"Comp": [int(nn[:, 0].min()), int(nn[:, 0].max())], "Coop": [int(nn[:, 1].min()), int(nn[:, 1].max())]}}


def exact_permutation(values, observed):
    total = math.comb(20, 10)
    assignment = np.fromiter(chain.from_iterable(combinations(range(20), 10)), dtype=np.int16).reshape(total, 10)
    selected_sum = values[assignment].sum(axis=1)
    statistics = selected_sum / 10 - (values.sum(axis=0) - selected_sum) / 10
    tolerance = 1e-12 * np.maximum(1., np.abs(observed))
    extreme = (np.abs(statistics) >= np.abs(observed)[None] - tolerance).sum(axis=0)
    p = extreme / total
    order = np.argsort(p)
    adjusted = np.maximum.accumulate((len(p) - np.arange(len(p))) * p[order])
    holm = np.empty_like(p)
    holm[order] = np.minimum(1., adjusted)
    return total, extreme, p, holm


def write_csv(path, rows):
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    with (ROOT / "cpr_empirical/conditions.csv").open() as f:
        conditions = {r["subject"]: r["condition"] for r in csv.DictReader(f) if r["group"] == "two"}
    design = source_design(conditions)
    with (ROOT / "cpr_redefinition/harvest_asm/summary.csv").open() as f:
        rounds = [r for r in csv.DictReader(f) if r["group"] == "two" and r["drive_grains"] == "8"]
    with (ROOT / "cpr_redefinition/harvest_asm/events.csv").open() as f:
        events = defaultdict(list)
        for r in csv.DictReader(f):
            if r["group"] == "two":
                events[r["trial"]].append(r)
    require(len(rounds) == 157, "Two-player main-sample round count differs")
    by_pair = defaultdict(list)
    for row in rounds:
        subject = row["subject"]
        require(row["condition"] == conditions[subject], "A pair changes condition across rounds")
        erows = events[row["trial"]]
        K = int(row["harvest_count"])
        v = int(row["total_topplings"]) - K
        nontrivial = sum(int(e["topplings"]) > 1 for e in erows)
        area = max(int(e["area"]) for e in erows)
        require(K == len(erows) > 0 and v >= 0, "Invalid event/harvest totals")
        require(nontrivial == int(row["nonlocal_avalanche_count"]) and area == int(row["max_avalanche_area"]), "Event-derived metric differs from summary")
        by_pair[subject].append(np.array([K, v, v / K, nontrivial / K, area], dtype=float))
    pair_ids = sorted(by_pair)
    require(pair_ids == sorted(conditions) and len(pair_ids) == 20, "Pair IDs differ")
    values = np.stack([np.mean(by_pair[subject], axis=0) for subject in pair_ids])
    condition_array = np.array([conditions[s] for s in pair_ids])
    comp, coop = values[condition_array == "Comp"], values[condition_array == "Coop"]
    require(len(comp) == len(coop) == 10, "Expected 10/10 pairs")
    observed = coop.mean(axis=0) - comp.mean(axis=0)
    pairs_boot = pair_bootstrap(comp, coop)
    components = design["connected_components_under_same_initials_same_person_assumption"]
    cluster_boot = component_bootstrap(values, pair_ids, conditions, components)
    permutations, extreme, p, holm = exact_permutation(values, observed)
    repeated_pairs = set(design["pairs_touching_any_reused_initial"])
    strict_comp = values[(condition_array == "Comp") & np.array([s not in repeated_pairs for s in pair_ids])]
    strict_coop = values[(condition_array == "Coop") & np.array([s not in repeated_pairs for s in pair_ids])]
    comparison = []
    for j, metric in enumerate(METRICS):
        strict = {"Comp_n_pairs": len(strict_comp), "Coop_n_pairs": len(strict_coop),
                  "Comp_mean": float(strict_comp[:, j].mean()) if len(strict_comp) else None,
                  "Coop_mean": float(strict_coop[:, j].mean()) if len(strict_coop) else None,
                  "Coop_minus_Comp": float(strict_coop[:, j].mean() - strict_comp[:, j].mean()) if len(strict_comp) and len(strict_coop) else None,
                  "Comp_median": float(np.median(strict_comp[:, j])) if len(strict_comp) else None,
                  "Coop_median": float(np.median(strict_coop[:, j])) if len(strict_coop) else None}
        comparison.append({"metric": metric, "Comp_mean": float(comp[:, j].mean()), "Coop_mean": float(coop[:, j].mean()),
                           "Comp_median": float(np.median(comp[:, j])), "Coop_median": float(np.median(coop[:, j])),
                           "Comp_pair_range": [float(comp[:, j].min()), float(comp[:, j].max())],
                           "Coop_pair_range": [float(coop[:, j].min()), float(coop[:, j].max())],
                           "Coop_minus_Comp_mean": float(observed[j]),
                           "pair_bootstrap_mean_difference_CI95": pairs_boot["difference_mean"][j].tolist(),
                           "pair_bootstrap_Comp_mean_CI95": pairs_boot["Comp_mean"][j].tolist(),
                           "pair_bootstrap_Coop_mean_CI95": pairs_boot["Coop_mean"][j].tolist(),
                           "Coop_minus_Comp_median": float(np.median(coop[:, j]) - np.median(comp[:, j])),
                           "pair_bootstrap_median_difference_CI95": pairs_boot["difference_median"][j].tolist(),
                           "component_bootstrap_mean_difference_CI95": cluster_boot["difference_mean"][j].tolist(),
                           "component_bootstrap_Comp_mean_CI95": cluster_boot["Comp_mean"][j].tolist(),
                           "component_bootstrap_Coop_mean_CI95": cluster_boot["Coop_mean"][j].tolist(),
                           "exact_pair_label_permutation_extreme_count": int(extreme[j]),
                           "exact_pair_label_permutation_p_reference": float(p[j]),
                           "holm_5_metrics_p_reference": float(holm[j]),
                           "exclude_all_reused_initial_pairs": strict})
    pair_rows = [{"subject": subject, "condition": conditions[subject], "n_rounds": len(by_pair[subject]),
                  **{metric: float(values[i, j]) for j, metric in enumerate(METRICS)}} for i, subject in enumerate(pair_ids)]
    design["round_counts_by_pair"] = {s: len(by_pair[s]) for s in pair_ids}
    design["main_rounds_by_condition"] = {condition: sum(len(by_pair[s]) for s in pair_ids if conditions[s] == condition) for condition in ("Comp", "Coop")}
    flat_rows = [{k: v for k, v in row.items() if not isinstance(v, (list, dict))} | {
                    "pair_CI_low": row["pair_bootstrap_mean_difference_CI95"][0], "pair_CI_high": row["pair_bootstrap_mean_difference_CI95"][1],
                    "component_CI_low": row["component_bootstrap_mean_difference_CI95"][0], "component_CI_high": row["component_bootstrap_mean_difference_CI95"][1]}
                 for row in comparison]
    result = {"design": design,
              "estimand": "For each metric, compute each round first, average available rounds within pair, then weight pairs equally within condition. The reported difference is Coop minus Comp.",
              "metrics": {"K": "harvests per round", "v": "secondary/cascade model topplings per round: u-K", "v_per_K": "within-round v/K, then pair mean",
                          "cascade_fraction": "within-round fraction of harvest events with q8 topplings>1, then pair mean",
                          "max_event_area_u": "within-round maximum event area (Delta u>0), including the guaranteed source firing, then pair mean"},
              "bootstrap": {"resamples": B, "seed": SEED, "interval": "two-sided 95% percentile, NumPy linear quantiles",
                            "pair": "Resample 10 pair means with replacement separately within Comp and Coop. Requires pair independence.",
                            "component": "Assume identical two-letter initials denote identical people; resample the connected components with replacement as intact clusters. Re-average original pair means with each condition's resampled pair count as denominator. This is an identity-assumption sensitivity, not evidence that participants actually repeat.",
                            "component_count": cluster_boot["components"], "component_valid_resamples": cluster_boot["valid_resamples"],
                            "component_rejected_empty_condition_resamples": cluster_boot["rejected_empty_condition_resamples"],
                            "component_resampled_pair_count_range": cluster_boot["resampled_pair_count_range"]},
              "permutation": {"assignments": permutations, "statistic": "absolute difference between condition means of pair means",
                              "tail": "two-sided >= observed magnitude, includes ties; exhaustive enumeration, no Monte Carlo +1 correction",
                              "status": "reference only: label exchangeability/random assignment and human independence are unverified",
                              "multiplicity": "Five exploratory metrics; no prespecified primary. Holm values are also reference-only and do not fix uncertain independence."},
              "strict_exclusion": {"excluded_pairs": sorted(repeated_pairs), "kept_pairs": [s for s in pair_ids if s not in repeated_pairs],
                                   "interpretation": "Drop every pair incident to a repeated-initial edge. This may discard different people with colliding initials and changes sample composition; descriptive sensitivity only."},
              "comparison": comparison,
              "interpretation_notes": ["A larger K changes the dose into this model. v/K is not a full adjustment because cascades grow nonlinearly with accumulated input and spatial concentration.",
                                       "Maximum event area also has more opportunities to be large when K is larger. Event fraction can depend on how far the field has been driven.",
                                       "A fixed-harvest-prefix comparison (for example 90 events, below the observed minimum94) would compare equal input budgets; it would address a different estimand.",
                                       "These are model outcomes from empirical harvests, not observed token-regeneration cascades or a causal estimate of cooperation."],
              "sources": [{"path": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in (
                  ROOT / "cpr_empirical/conditions.csv", ROOT / "cpr_redefinition/harvest_asm/summary.csv", ROOT / "cpr_redefinition/harvest_asm/events.csv")]}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "independent_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n")
    write_csv(OUT / "pair_metrics.csv", pair_rows)
    write_csv(OUT / "comparison.csv", flat_rows)
    print(json.dumps({"design": design, "bootstrap": result["bootstrap"], "comparison": comparison,
                      "strict_exclusion": result["strict_exclusion"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
