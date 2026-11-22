"""Fixed-count and spatial-permutation controls for the existing harvest ASM.

Read only previously derived summary/events/NPZ, never raw participant logs.
Write only within this script's output directory. The field is the unchanged
zero-background, fixed Moore graph with threshold8 and offboard sink.
Direct-neighbor input sends one integer grain in each of eight directions per
harvest; its odometer v equals the existing q8 source-input u minus K.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import csv
import hashlib
import json
from pathlib import Path
import sys
import time

import numpy as np

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "cpr_redefinition/harvest_asm"


def neighbors(a):
    """Moore sum on the last two axes, supporting batches of boards."""
    b = np.zeros_like(a)
    b[..., 1:, 1:] += a[..., :-1, :-1]
    b[..., 1:, :] += a[..., :-1, :]
    b[..., 1:, :-1] += a[..., :-1, 1:]
    b[..., :, 1:] += a[..., :, :-1]
    b[..., :, :-1] += a[..., :, 1:]
    b[..., :-1, 1:] += a[..., 1:, :-1]
    b[..., :-1, :] += a[..., 1:, :]
    b[..., :-1, :-1] += a[..., 1:, 1:]
    return b


def stabilize(a):
    """Exact integer stabilization, with all boards sharing parallel rounds."""
    a = np.asarray(a, dtype=np.int64)
    z = a.copy()
    u = np.zeros_like(z)
    deficit = 8 - neighbors(np.ones(z.shape[-2:], dtype=np.int64))
    sink = np.zeros(z.shape[:-2], dtype=np.int64)
    rounds = np.zeros_like(sink)
    iterations = 0
    while True:
        active = np.any(z >= 8, axis=(-2, -1))
        if not np.any(active):
            break
        batch = z // 8
        z -= 8 * batch
        z += neighbors(batch)
        u += batch
        sink += np.sum(batch * deficit, axis=(-2, -1))
        rounds += active
        iterations += 1
        if iterations > 100000:
            raise RuntimeError("Finite stabilization guard exceeded")
    assert np.all((0 <= z) & (z < 8))
    assert np.array_equal(a.sum(axis=(-2, -1)), z.sum(axis=(-2, -1)) + sink)
    assert np.array_equal(z, a - 8 * u + neighbors(u))
    return z, u, sink, rounds


def read_csv(path):
    with Path(path).open(encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path, rows):
    rows = list(rows)
    if not rows:
        raise ValueError("Empty CSV")
    with Path(path).open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def basic_key(row):
    return {"trial": row["trial"], "condition": row["condition"],
            "pair_id": "two_" + row["subject"], "subject": row["subject"],
            "round": int(row["round"])}


def descriptive_groups(rows, metrics, stem, out):
    """Average trials within pair, then weight the ten pair IDs equally."""
    buckets = defaultdict(list)
    for row in rows:
        buckets[(row["condition"], row["pair_id"])].append(row)
    pairs = []
    for (condition, pair), trials in sorted(buckets.items()):
        pairs.append({"condition": condition, "pair_id": pair, "n_trials": len(trials),
                      **{metric: float(np.mean([r[metric] for r in trials])) for metric in metrics}})
    groups = []
    for condition in ("Comp", "Coop"):
        selected = [p for p in pairs if p["condition"] == condition]
        assert len(selected) == 10
        for metric in metrics:
            values = np.asarray([p[metric] for p in selected], dtype=float)
            groups.append({"condition": condition, "metric": metric,
                           "n_pair_ids": len(values), "n_trials": sum(p["n_trials"] for p in selected),
                           "pair_equal_mean": float(values.mean()),
                           "pair_mean_median": float(np.median(values)),
                           "pair_mean_sd": float(values.std(ddof=1)),
                           "pair_mean_min": float(values.min()), "pair_mean_max": float(values.max())})
    contrasts = []
    lookup = {(r["condition"], r["metric"]): r["pair_equal_mean"] for r in groups}
    for metric in metrics:
        comp, coop = lookup[("Comp", metric)], lookup[("Coop", metric)]
        contrasts.append({"analysis": stem, "metric": metric,
                          "Comp_pair_equal_mean": comp, "Coop_pair_equal_mean": coop,
                          "Coop_minus_Comp": coop - comp})
    write_csv(out / f"{stem}_pairs.csv", pairs)
    write_csv(out / f"{stem}_group_summary.csv", groups)
    return contrasts


def prefix_trial(row, events, data, prefix, out):
    xx, yy = data["x_coords"], data["y_coords"]
    xi = {int(x): i for i, x in enumerate(xx)}
    yi = {int(y): i for i, y in enumerate(yy)}
    shape = (len(xx), len(yy))
    z = np.zeros(shape, dtype=np.int64)
    v = np.zeros_like(z)
    counts = np.zeros_like(z)
    deficit = 8 - neighbors(np.ones(shape, dtype=np.int64))
    direct_sink = cascade_sink = 0
    ev_topplings, ev_v_areas, ev_u_areas, ev_times, ev_xy = [], [], [], [], []
    for event in events[:prefix]:
        hx, hy = int(event["x"]), int(event["y"])
        ix, iy = xi[hx], yi[hy]
        counts[ix, iy] += 1
        impulse = np.zeros_like(z)
        impulse[ix, iy] = 1
        z += neighbors(impulse)
        direct_sink += int(deficit[ix, iy])
        z, dv, sink, _ = stabilize(z)
        v += dv
        cascade_sink += int(sink)
        du = dv.copy()
        du[ix, iy] += 1
        vt = int(dv.sum())
        ua = int(np.count_nonzero(du))
        assert vt + 1 == int(event["topplings"])
        assert ua == int(event["area"])
        assert int(sink) + int(deficit[ix, iy]) == int(event["sink_grains"])
        ev_topplings.append(vt)
        ev_v_areas.append(int(np.count_nonzero(dv)))
        ev_u_areas.append(ua)
        ev_times.append(float(event["time"]))
        ev_xy.append((hx, hy))
    u = v + counts
    bulk_z, bulk_u, bulk_sink, _ = stabilize(8 * counts)
    assert np.array_equal(z, bulk_z) and np.array_equal(u, bulk_u)
    assert direct_sink + cascade_sink == int(bulk_sink)
    assert 8 * prefix == int(z.sum()) + direct_sink + cascade_sink
    ev_topplings = np.asarray(ev_topplings, dtype=np.int64)
    row_out = {**basic_key(row), "total_harvests": len(events), "prefix_harvests": prefix,
               "t_start": float(row["t_start"]), "first_harvest_time": ev_times[0],
               "prefix_last_harvest_time": ev_times[-1],
               "prefix_elapsed_s": ev_times[-1] - float(row["t_start"]),
               "v_total": int(v.sum()), "v_per_harvest": float(v.sum()) / prefix,
               "u_total": int(u.sum()), "nontrivial_events": int(np.count_nonzero(ev_topplings)),
               "nontrivial_fraction": float(np.count_nonzero(ev_topplings)) / prefix,
               "max_event_u_area": max(ev_u_areas), "max_event_v_area": max(ev_v_areas),
               "max_event_v_topplings": int(ev_topplings.max()),
               "v_active_cells": int(np.count_nonzero(v)),
               "distinct_harvest_cells": int(np.count_nonzero(counts)),
               "direct_sink_grains": direct_sink, "cascade_sink_grains": cascade_sink,
               "retained_grains": int(z.sum())}
    np.savez_compressed(out / "prefix90" / f"{row['trial']}.npz",
                        harvest=counts, height_grains=z, u=u, v=v, x_coords=xx, y_coords=yy,
                        event_times=np.asarray(ev_times), event_xy=np.asarray(ev_xy),
                        event_v_topplings=ev_topplings, event_v_areas=np.asarray(ev_v_areas),
                        event_u_areas=np.asarray(ev_u_areas),
                        prefix_last_harvest_time=np.asarray(ev_times[-1]),
                        direct_sink_grains=np.asarray(direct_sink), cascade_sink_grains=np.asarray(cascade_sink))
    return row_out


def shuffle_trial(row, data, repeats, seed, out):
    counts = data["harvest"][-1].astype(np.int64)
    actual_u = data["odometer"][1, -1].astype(np.int64)
    actual_v = actual_u - counts
    assert np.all(actual_v >= 0)
    actual_z, checked_u, actual_sink, _ = stabilize(8 * counts)
    assert np.array_equal(checked_u, actual_u)
    assert np.array_equal(actual_z, data["height_grains"][1, -1])
    entropy = [seed, int(row["subject"]), int(row["round"])]
    rng = np.random.default_rng(np.random.SeedSequence(entropy))
    shuffled = np.stack([rng.permutation(counts.ravel()).reshape(counts.shape) for _ in range(repeats)])
    assert np.all(np.sort(shuffled.reshape(repeats, -1), axis=1) == np.sort(counts.ravel()))
    shuffle_z, shuffle_u, shuffle_sink, waves = stabilize(8 * shuffled)
    shuffle_v = shuffle_u - shuffled
    assert np.all(shuffle_v >= 0)
    total = int(counts.sum())
    actual_ut, actual_vt = int(actual_u.sum()), int(actual_v.sum())
    shuffle_ut = shuffle_u.sum(axis=(-2, -1))
    shuffle_vt = shuffle_v.sum(axis=(-2, -1))
    assert np.array_equal(shuffle_ut - shuffle_vt, np.full(repeats, total))
    mean_u, mean_v = shuffle_u.mean(axis=0), shuffle_v.mean(axis=0)
    expected_ut, expected_vt = float(shuffle_ut.mean()), float(shuffle_vt.mean())
    row_out = {**basic_key(row), "harvest_count": total, "shuffles": repeats,
               "seed_base": seed, "seed_pair": int(row["subject"]), "seed_round": int(row["round"]),
               "actual_u_total": actual_ut, "actual_v_total": actual_vt,
               "actual_v_per_harvest": actual_vt / total,
               "shuffle_mean_u_total": expected_ut, "shuffle_mean_v_total": expected_vt,
               "shuffle_mean_v_per_harvest": expected_vt / total,
               "u_total_minus_shuffle_mean": actual_ut - expected_ut,
               "v_total_minus_shuffle_mean": actual_vt - expected_vt,
               "v_per_harvest_minus_shuffle_mean": (actual_vt - expected_vt) / total,
               "shuffle_sd_v_total": float(shuffle_vt.std(ddof=1)),
               "shuffle_min_v_total": int(shuffle_vt.min()), "shuffle_max_v_total": int(shuffle_vt.max()),
               "actual_sink_grains": int(actual_sink), "shuffle_mean_sink_grains": float(shuffle_sink.mean()),
               "shuffle_max_parallel_rounds": int(waves.max())}
    np.savez_compressed(out / "spatial99" / f"{row['trial']}.npz",
                        harvest=counts.astype(np.int16), actual_u=actual_u.astype(np.int32),
                        actual_v=actual_v.astype(np.int32), actual_height_grains=actual_z.astype(np.int8),
                        shuffled_harvest=shuffled.astype(np.int16), shuffled_u=shuffle_u.astype(np.int32),
                        shuffled_v=shuffle_v.astype(np.int32), shuffled_height_grains=shuffle_z.astype(np.int8),
                        mean_shuffled_u=mean_u, mean_shuffled_v=mean_v,
                        difference_u=actual_u - mean_u, difference_v=actual_v - mean_v,
                        shuffled_u_total=shuffle_ut, shuffled_v_total=shuffle_vt,
                        shuffled_v_per_harvest=shuffle_vt / total,
                        x_coords=data["x_coords"], y_coords=data["y_coords"],
                        seed_entropy=np.asarray(entropy))
    return row_out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--prefix", type=int, default=90)
    parser.add_argument("--shuffles", type=int, default=99)
    parser.add_argument("--seed", type=int, default=20261121)
    args = parser.parse_args()
    if args.prefix != 90 or args.shuffles != 99:
        raise ValueError("This prespecified comparison uses prefix90 and 99 shuffles")
    start = time.perf_counter()
    args.out.mkdir(parents=True, exist_ok=True)
    for folder in ("prefix90", "spatial99"):
        (args.out / folder).mkdir(exist_ok=True)
    rows = sorted([r for r in read_csv(args.source / "summary.csv")
                   if r["group"] == "two" and r["drive_grains"] == "8"], key=lambda r: r["trial"])
    assert len(rows) == 157
    assert {c: sum(r["condition"] == c for r in rows) for c in ("Comp", "Coop")} == {"Comp": 79, "Coop": 78}
    by_trial = defaultdict(list)
    for event in read_csv(args.source / "events.csv"):
        if event["group"] == "two":
            by_trial[event["trial"]].append(event)
    all_data = {}
    for row in rows:
        events = sorted(by_trial[row["trial"]], key=lambda r: int(r["event_index"]))
        by_trial[row["trial"]] = events
        assert len(events) == int(row["harvest_count"]) >= args.prefix
        assert [int(e["event_index"]) for e in events] == list(range(len(events)))
        assert all(e["condition"] == row["condition"] for e in events)
        assert all(float(a["time"]) <= float(b["time"]) for a, b in zip(events, events[1:]))
        with np.load(args.source / "trials" / f"{row['trial']}.npz") as data:
            all_data[row["trial"]] = {k: data[k] for k in ("x_coords", "y_coords", "harvest", "odometer", "height_grains")}
        assert int(all_data[row["trial"]]["harvest"][-1].sum()) == len(events)
    prefix_rows = [prefix_trial(r, by_trial[r["trial"]], all_data[r["trial"]], args.prefix, args.out) for r in rows]
    write_csv(args.out / "prefix90_trials.csv", prefix_rows)
    prefix_metrics = ["v_total", "v_per_harvest", "nontrivial_events", "nontrivial_fraction", "max_event_u_area",
                      "max_event_v_area", "max_event_v_topplings", "prefix_elapsed_s", "distinct_harvest_cells"]
    contrasts = descriptive_groups(prefix_rows, prefix_metrics, "prefix90", args.out)
    print(json.dumps({"stage": "prefix90_complete", "trials": len(prefix_rows),
                      "seconds": time.perf_counter() - start, "contrasts": contrasts}, ensure_ascii=False), flush=True)
    shuffle_rows = []
    for idx, row in enumerate(rows, 1):
        shuffle_rows.append(shuffle_trial(row, all_data[row["trial"]], args.shuffles, args.seed, args.out))
        if idx % 10 == 0 or idx == len(rows):
            print(f"Spatial permutations: {idx}/{len(rows)} trials, {time.perf_counter()-start:.1f}s", flush=True)
    write_csv(args.out / "spatial99_trials.csv", shuffle_rows)
    shuffle_metrics = ["actual_v_total", "actual_v_per_harvest", "shuffle_mean_v_total", "shuffle_mean_v_per_harvest",
                       "v_total_minus_shuffle_mean", "v_per_harvest_minus_shuffle_mean", "harvest_count"]
    contrasts += descriptive_groups(shuffle_rows, shuffle_metrics, "spatial99", args.out)
    write_csv(args.out / "group_differences.csv", contrasts)
    metadata = {
        "model": "Unchanged zero-background Moore ASM; threshold8, one grain per direction on each harvest; offboard directions sink; v=u-K",
        "sample": {"trials": len(rows), "conditions": {"Comp": 79, "Coop": 78}, "pair_ids_per_condition": 10},
        "prefix": {"harvests": args.prefix, "definition": "First90 recorded successful harvests in the existing observation window; original event order including ties",
                   "meaning": "Matches input count, not elapsed time; ninety does not identify individual initial tokens",
                   "nontrivial_event": "Direct-neighbor v-event has positive toppling count, equivalent to q8 event topplings>1",
                   "maximum_area": "max_event_u_area includes the guaranteed source site as in previous q8 events; max_event_v_area is also supplied"},
        "spatial": {"replicates_per_trial": args.shuffles, "seed_base": args.seed,
                    "seed_rule": "NumPy SeedSequence([base_seed, integer_pair_id, round])",
                    "operation": "Uniformly permute full-terminal K map positions, retaining its histogram and total; each replicate starts at zero on the same graph",
                    "scalar_difference": "Actual total u or v minus mean shuffle total; v/K difference is the same v difference divided by fixed trial K total",
                    "map_difference": "Actual u or v field minus its own shuffle mean field; separate differences because local K positions change",
                    "interpretation": "Descriptive sensitivity within this model, not a causal adjustment, CPR-feasible counterfactual, or significance test"},
        "aggregation": "Mean trials within each pair_id, then average ten pair_id means equally per condition; descriptive only, no independence assumption or p-values",
        "participant_overlap": "Pair IDs may share participant labels according to separate audit; inferential claims are intentionally omitted",
        "checks": {"all_prefix_events_match_existing_q8_topplings_area_sink": True,
                   "all_prefix_chronological_direct_matches_bulk_q8": True,
                   "all_actual_terminal_fields_match_existing_npz": True,
                   "all_shuffle_histograms_and_totals_exact": True,
                   "all_stabilizations_integer_mass_and_local_laplacian_exact": True},
        "inputs_sha256": {name: hashlib.sha256((args.source / name).read_bytes()).hexdigest()
                          for name in ("summary.csv", "events.csv", "analyze_harvest_asm.py")},
        "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "wall_seconds": time.perf_counter() - start,
    }
    (args.out / "metadata.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"stage": "complete", "seconds": metadata["wall_seconds"],
                      "contrasts": [r for r in contrasts if r["analysis"] == "spatial99"]}, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
