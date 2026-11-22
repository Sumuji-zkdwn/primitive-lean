"""Fixed Moore ASM driven by recorded harvests, with two explicit input rules.

q=1: one harvest supplies one grain, threshold eight.
q=8: one harvest supplies one toppling's worth, threshold eight.
In the second convention h=z/8 has threshold one and sends 1/8 each direction.
Changing q is a modelling choice, NOT a unit conversion of the first model.
Occupancy never gates this independent field. Outside directions go to a sink.
"""
from __future__ import annotations
import csv
import hashlib
import io
import json
from pathlib import Path
import re
from zipfile import ZipFile
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
FOCUS = {"two_04_r6", "one_15_r3", "two_18_r7"}


def neighbors(values):
    p = np.pad(values, 1)
    n = values.shape[0]
    result = np.zeros_like(values)
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            if dx or dy:
                result += p[1+dx:1+dx+n, 1+dy:1+dy+n]
    return result


def stabilize(height):
    """Parallel legal batches; all arithmetic is integer and mass exact."""
    z = np.array(height, dtype=np.int64, copy=True)
    u = np.zeros_like(z)
    deficit = 8 - neighbors(np.ones_like(z))
    loss = waves = 0
    while np.any(z >= 8):
        batch = z // 8
        z -= 8 * batch
        z += neighbors(batch)
        u += batch
        loss += int((batch * deficit).sum())
        waves += 1
        if waves > 100000:
            raise RuntimeError("Stabilization did not finish within finite guard")
    if np.any(z < 0) or int(height.sum()) != int(z.sum()) + loss:
        raise AssertionError("Integer conservation failed")
    return z, u, loss, waves


def write_csv(path, rows):
    with Path(path).open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)


def analyze_trial(row, harvest):
    trial = row["trial"]
    with np.load(ROOT / "cpr_patterns" / "empirical" / row["file"]) as z:
        old = {k: z[k] for k in z.files}
    if trial in FOCUS:
        with np.load(ROOT / "cpr_patterns_v2/temporal/trials" / f"{trial}.npz") as z:
            observed = {k: z[k] for k in ("times", "observed_times", "x", "x_coords", "y_coords", "t_start")}
    else:
        observed = {k: old[k] for k in ("times", "observed_times", "x", "x_coords", "y_coords", "t_start")}
    times = observed["times"]
    start, end = float(old["t_start"]), float(times[-1])
    xx, yy = old["x_coords"], old["y_coords"]
    nx = {int(x): i for i, x in enumerate(xx)}
    ny = {int(y): i for i, y in enumerate(yy)}
    # Observation-window harvests, matching the previous empirical count.
    events = [(ht, order, nx[hx], ny[hy], hx, hy)
              for order, (ht, hx, hy) in enumerate(harvest) if start <= ht < end]
    events.sort(key=lambda e: (e[0], e[1]))
    size = len(xx)
    z = np.zeros((2, size, size), dtype=np.int64)
    u = np.zeros_like(z); sink = np.zeros(2, dtype=np.int64)
    counts = np.zeros((size, size), dtype=np.int64)
    samples = {k: [] for k in ("height_grains", "odometer", "sink_grains", "harvest")}
    event_rows = []
    largest = None
    index = 0
    for readout in times:
        # A saved board at exactly ht precedes that harvest; readout is [start,t).
        while index < len(events) and events[index][0] < readout:
            ht, order, ix, iy, hx, hy = events[index]
            counts[ix, iy] += 1
            z[0, ix, iy] += 1
            z0, du0, loss0, _ = stabilize(z[0]); z[0] = z0; u[0] += du0; sink[0] += loss0
            before = z[1].copy()
            z[1, ix, iy] += 8
            z1, du, loss, waves = stabilize(z[1]); z[1] = z1; u[1] += du; sink[1] += loss
            topplings, area = int(du.sum()), int(np.count_nonzero(du))
            coords = np.argwhere(du > 0)
            radius = int(np.max(np.abs(coords - [ix, iy]))) if len(coords) else 0
            record = {"trial": trial, "group": row["group"], "condition": row["condition"],
                      "event_index": index, "logged_row_index": order, "time": ht,
                      "x": hx, "y": hy, "topplings": topplings, "area": area,
                      "parallel_rounds": waves, "radius_chebyshev": radius, "sink_grains": loss}
            event_rows.append(record)
            if largest is None or (area, topplings) > (largest[0]["area"], largest[0]["topplings"]):
                largest = (record, du.copy(), before, z1.copy())
            index += 1
        assert np.array_equal(z, np.array([1, 8])[:, None, None]*counts - 8*u + np.stack([neighbors(ui) for ui in u]))
        assert np.array_equal(np.array([1, 8])*counts.sum(), z.sum(axis=(-2,-1)) + sink)
        for key, value in [("height_grains", z), ("odometer", u), ("sink_grains", sink), ("harvest", counts)]:
            samples[key].append(value.copy())
    arrays = dict(observed)
    arrays.update({key: np.stack(values, axis=1 if key != "harvest" else 0) for key, values in samples.items()})
    arrays["drive_grains"] = np.array([1, 8])
    arrays["initial_height_grains"] = np.zeros((size, size), dtype=np.int64)
    assert index == len(events)
    assert np.array_equal(counts, old["harvest"][-1])
    # Batch the same inputs and independently check the abelian endpoint within this engine.
    for qi, q in enumerate((1, 8)):
        bulk_h, bulk_u, bulk_sink, _ = stabilize(q * counts)
        assert np.array_equal(bulk_h, z[qi]) and np.array_equal(bulk_u, u[qi]) and bulk_sink == sink[qi]
    if largest is not None:
        arrays.update(largest_avalanche_u=largest[1], largest_avalanche_before=largest[2],
                      largest_avalanche_after=largest[3], largest_avalanche_time=np.array(largest[0]["time"]),
                      largest_avalanche_source=np.array([largest[0]["x"], largest[0]["y"]]),
                      largest_avalanche_event_index=np.array(largest[0]["event_index"]))
    checkpoint_ids = [int(np.flatnonzero(times == t)[0]) for t in old["times"]]
    checkpoint = {}
    for key, val in arrays.items():
        if key in ("height_grains", "odometer", "sink_grains"):
            checkpoint[key] = val[:, checkpoint_ids]
        elif key in ("times", "observed_times", "x", "harvest"):
            checkpoint[key] = val[checkpoint_ids]
        else:
            checkpoint[key] = val
    assert np.array_equal(checkpoint["harvest"], old["harvest"])
    summary = []
    for qi, q in enumerate((1, 8)):
        summary.append({"trial": trial, "group": row["group"], "subject": row["subject"],
                        "round": row["round"], "condition": row["condition"], "drive_grains": q,
                        "side": size, "harvest_count": len(events), "input_grains": q*len(events),
                        "retained_grains": int(z[qi].sum()), "sink_grains": int(sink[qi]),
                        "total_topplings": int(u[qi].sum()), "toppled_cells": int(np.count_nonzero(u[qi])),
                        "toppled_unharvested_cells": int(np.count_nonzero((u[qi] > 0) & (counts == 0))),
                        "max_avalanche_topplings": max(r["topplings"] for r in event_rows) if qi == 1 else 0,
                        "max_avalanche_area": max(r["area"] for r in event_rows) if qi == 1 else 0,
                        "max_avalanche_radius": max(r["radius_chebyshev"] for r in event_rows) if qi == 1 else 0,
                        "nonlocal_avalanche_count": sum(r["area"] > 1 for r in event_rows) if qi == 1 else 0,
                        "t_start": start, "t_end": end})
    return checkpoint, arrays if trial in FOCUS else None, summary, event_rows


def main():
    metadata = json.loads((ROOT / "cpr_transport/metadata.json").read_text())
    selected = {r["trial"]: r for r in metadata["trials"]}
    all_rows = []; all_events = []; seen = []
    for sub in ("trials", "fulltime"):
        (OUT / sub).mkdir(parents=True, exist_ok=True)
    for group, source in zip(("one", "two"), metadata["source_archives"]):
        path = ROOT / "cpr_empirical_sources" / source["filename"]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == source["sha256"]
        with ZipFile(path) as archive:
            names = sorted(n for n in archive.namelist() if "/03_rawdata/" in n and n.endswith("/Harvest.csv"))
            for name in names:
                pieces = name.split("/")
                subject = pieces[-3].split("_", 1)[0]
                rnd = int(re.fullmatch(r"round(\d+)", pieces[-2]).group(1))
                trial = f"{group}_{subject}_r{rnd}"
                if trial not in selected:
                    continue
                reader = csv.reader(io.StringIO(archive.read(name).decode("utf-8-sig")))
                next(reader)
                harvest = [(float(r[0]), int(float(r[2])), int(float(r[3]))) for r in reader if r]
                checkpoints, full, rows, events = analyze_trial(selected[trial], harvest)
                np.savez_compressed(OUT / "trials" / f"{trial}.npz", **checkpoints)
                if full is not None:
                    np.savez_compressed(OUT / "fulltime" / f"{trial}.npz", **full)
                all_rows.extend(rows); all_events.extend(events); seen.append(trial)
                if len(seen) % 80 == 0:
                    print(f"Harvest ASM {len(seen)}/397 trials", flush=True)
    assert set(seen) == set(selected) and len(all_events) == 41431
    assert all(r["total_topplings"] == 0 for r in all_rows if r["drive_grains"] == 1)
    write_csv(OUT / "summary.csv", all_rows)
    write_csv(OUT / "events.csv", all_events)
    q8 = [r for r in all_rows if r["drive_grains"] == 8]
    pooled = {k: sum(r[k] for r in q8) for k in ("harvest_count", "input_grains", "retained_grains", "sink_grains",
                                                "total_topplings", "toppled_cells", "toppled_unharvested_cells", "nonlocal_avalanche_count")}
    candidates = sorted(q8, key=lambda r: (-r["max_avalanche_area"], -r["max_avalanche_topplings"], r["trial"]))[:12]
    info = {
        "definition": "Fixed open Moore grid with eight outgoing directions; missing directions feed a sink; initial z=0; stable z in 0..7",
        "drive_rules": {"1": "One harvest adds one grain, threshold8", "8": "One harvest supplies one toppling's worth; h=z/8 has input1, threshold1, transfer1/8 per direction"},
        "rule_difference": "q8 is an eightfold drive relative to threshold compared with q1; this is an explicit alternative event correspondence, not a mere change of units",
        "event_timing": "Use original logged harvest times and original row order on ties; stabilize completely after every harvest; each readout includes events [t_start, readout)",
        "physical_time": "Internal parallel rounds are computation steps, not seconds or observed biological/social cascades",
        "resource_relation": "Original occupancy retained for reference but never gates the independent ASM; generated topplings are not recorded CPR births",
        "endpoint_abelianness": "Given the initial grid, terminal h and cumulative odometer depend only on per-cell harvest totals. Intermediate avalanches depend on prefixes; ties follow logged order",
        "scope": "Experimental-drive model; no claim of a fitted CPR regeneration mechanism, criticality, or beautiful pattern prevalence",
        "source_archives": metadata["source_archives"], "main_trials": len(seen), "fulltime_trials": sorted(FOCUS),
        "q1_all_trials_zero_topplings": True, "q8_pooled": pooled,
        "q8_max_avalanche": max(all_events, key=lambda r: (r["area"], r["topplings"])),
        "candidate_rule": "Top12 by maximum event avalanche area, then maximum event topplings; descriptive, not beauty ranking",
        "candidates": candidates,
        "checks": {"mass_integer_exact": True, "local_laplacian_integer_exact": True, "chronological_vs_bulk_all397_both_q": True,
                   "harvest_maps_match_prior_all_checkpoints": True},
        "arrays": {"height_grains_and_odometer": "(drive,time,x,y); drive=[1,8]; original x outer,y inner",
                   "sink_grains": "(drive,time)", "harvest_and_observed_x": "(time,x,y)",
                   "largest_avalanche": "Within each trial, maximum area then topplings; before/after are q8 integer heights"},
        "code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (OUT / "metadata.json").write_text(json.dumps(info, ensure_ascii=False, indent=2)+"\n")
    print(json.dumps({"trials": len(seen), "q8_pooled": pooled, "max_avalanche": info["q8_max_avalanche"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
