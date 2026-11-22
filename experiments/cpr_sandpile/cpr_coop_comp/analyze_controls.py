"""Quantify two complementary input/placement sensitivities, without claiming causal adjustment."""
from pathlib import Path
import itertools
import json
import numpy as np

from analyze_conditions import read_csv, write_csv, dyad_means, descriptive


HERE = Path(__file__).resolve().parent
METRICS = ["prefix90_v", "placement_excess_v_per_K"]
DESCRIPTIVE = METRICS + ["prefix90_v_per_K", "prefix90_elapsed", "prefix90_cascade_fraction", "prefix90_max_u_area", "actual_v_per_K", "shuffle_mean_v_per_K"]


def main():
    prefix = read_csv(HERE / "controls/prefix90_trials.csv")
    spatial = {r["trial"]: r for r in read_csv(HERE / "controls/spatial99_trials.csv")}
    rows = []
    for r in prefix:
        s = spatial[r["trial"]]
        assert r["condition"] == s["condition"] and r["subject"] == s["subject"]
        rows.append({"trial": r["trial"], "subject": r["subject"], "condition": r["condition"], "round": int(r["round"]),
                     "prefix90_v": float(r["v_total"]), "prefix90_v_per_K": float(r["v_per_harvest"]),
                     "prefix90_elapsed": float(r["prefix_elapsed_s"]), "prefix90_cascade_fraction": float(r["nontrivial_fraction"]),
                     "prefix90_max_u_area": float(r["max_event_u_area"]),
                     "placement_excess_v_per_K": float(s["v_per_harvest_minus_shuffle_mean"]),
                     "actual_v_per_K": float(s["actual_v_per_harvest"]), "shuffle_mean_v_per_K": float(s["shuffle_mean_v_per_harvest"])})
    assert len(rows) == 157
    pairs = dyad_means(rows, DESCRIPTIVE)
    matrix = np.array([[r[m] for m in METRICS] for r in pairs])
    labels = np.array([r["condition"] == "Coop" for r in pairs])
    coop, comp = matrix[labels], matrix[~labels]
    delta = coop.mean(0) - comp.mean(0)
    assignments = np.array(list(itertools.combinations(range(20), 10)))
    sums = matrix[assignments].sum(1)
    perm = sums/10 - (matrix.sum(0)-sums)/10
    p = np.mean(np.abs(perm) >= np.abs(delta)[None, :] - 1e-11, 0)
    seed = 20261211
    rng = np.random.default_rng(seed)
    b = 100000
    bootstrap = coop[rng.integers(0,10,(b,10))].mean(1)-comp[rng.integers(0,10,(b,10))].mean(1)
    ci = np.quantile(bootstrap,[.025,.975],axis=0)

    audit = json.loads((HERE / "audit/independent_results.json").read_text())
    components = audit["design"]["connected_components_under_same_initials_same_person_assumption"]
    where = {r["subject"]: i for i,r in enumerate(pairs)}
    component_sums = []
    component_counts = []
    for component in components:
        indices = np.array([where[s] for s in component])
        component_sums.append(np.stack([matrix[indices[labels[indices]]].sum(0), matrix[indices[~labels[indices]]].sum(0)]))
        component_counts.append([int(labels[indices].sum()), int((~labels[indices]).sum())])
    cs = np.array(component_sums)
    cc = np.array(component_counts)
    ids = rng.integers(0,len(components),(b,len(components)))
    sampled_sums, sampled_counts = cs[ids].sum(1),cc[ids].sum(1)
    valid = np.all(sampled_counts>0,axis=1)
    bd = sampled_sums[valid,0]/sampled_counts[valid,0,None]-sampled_sums[valid,1]/sampled_counts[valid,1,None]
    cci = np.quantile(bd,[.025,.975],axis=0)

    core = read_csv(HERE / "condition_comparison.csv")
    all_ps = np.array([float(r["two_sided_exact_permutation_p"]) for r in core] + p.tolist())
    order=np.argsort(all_ps)
    holm=np.empty_like(all_ps)
    holm[order]=np.minimum(1.,np.maximum.accumulate(all_ps[order]*np.arange(len(all_ps),0,-1)))
    result = [{"metric":m,"Comp_mean":float(comp[:,j].mean()),"Coop_mean":float(coop[:,j].mean()),
               "difference_Coop_minus_Comp":float(delta[j]), "dyad_bootstrap_ci95":ci[:,j].tolist(),
               "same_initial_component_bootstrap_ci95":cci[:,j].tolist(),
               "exact_permutation_p_reference":float(p[j]), "holm_across_five_main_plus_two_controls_reference":float(holm[len(core)+j])}
              for j,m in enumerate(METRICS)]
    all_holm = [{"metric":r["metric"],"exact_permutation_p_reference":float(all_ps[i]),"holm_seven_reference":float(holm[i])} for i,r in enumerate(core+result)]
    write_csv(HERE / "control_round_metrics.csv",rows)
    write_csv(HERE / "control_dyad_metrics.csv",pairs)
    output = {"results":result,"descriptive":descriptive(pairs,DESCRIPTIVE),"holm_seven":all_holm,
              "method":{"bootstrap_seed":seed,"bootstrap_draws":b,"exact_label_assignments":len(assignments),
                        "component_resamples_with_both_conditions":int(valid.sum()),
                        "component_identity_assumption":"Equal two-letter initial strings denote the same person; uncertain, for sensitivity only",
                        "prefix90":"Every one of157 trials has at least94 harvests;90 chosen to match initial token count before analyzing its output; same input count, not same elapsed time",
                        "spatial99":"Each round's K histogram and total preserved,99 uniform location permutations; empirical minus model permutation mean; no behavioral null or causal adjustment",
                        "statistical_status":"Exploratory; p values reference-only with dyad-independence/exchangeability assumptions; seven-test Holm includes all5 main metrics and both control metrics"}}
    (HERE / "control_comparison.json").write_text(json.dumps(output,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps({"results":result,"holm_seven":all_holm,"elapsed":{c:output['descriptive'][c]['metrics']['prefix90_elapsed']['mean'] for c in ['Comp','Coop']}},ensure_ascii=False,indent=2))


if __name__ == "__main__": main()
