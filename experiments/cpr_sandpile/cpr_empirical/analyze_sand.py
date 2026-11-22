"""Apply an operational probability-sand ledger to sampled human CPR logs.

This is a derived observation-clock ledger, not a replay of Unity's hidden
coroutine timing. Original archives are read only. No participant names are
written to the outputs. See README/report for identification limitations.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import re
from pathlib import Path
from zipfile import ZipFile

import numpy as np


ARCHIVES = {"one": "01_expCPR_1player(2).zip", "two": "02_expCPR_2player(1).zip"}
PHASES = np.arange(8, dtype=float) / 8


def read_table(path):
    with Path(path).open(encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path, rows):
    if not rows:
        return
    keys = list(dict.fromkeys(k for row in rows for k in row))
    with Path(path).open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        w.writerows(rows)


def moore_counts(x):
    """Open rectangular Moore graph, arrays (..., width, height)."""
    w, h = x.shape[-2:]
    pads = [(0, 0)] * (x.ndim - 2) + [(1, 1), (1, 1)]
    padded = np.pad(x, pads)
    result = np.zeros_like(x, dtype=np.int16)
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            if dx or dy:
                result += padded[..., 1 + dx:1 + dx + w, 1 + dy:1 + dy + h]
    return result


def load_trial(z, name):
    raw = z.read(name)
    header = next(csv.reader(io.StringIO(raw.decode("utf-8-sig"))))
    coords = np.array([tuple(map(int, s.split("_")[1:])) for s in header[1:]])
    data = np.loadtxt(io.BytesIO(raw), delimiter=",", skiprows=1)
    t = data[:, 0]
    x = data[:, 1:]
    assert np.isfinite(data).all() and np.all(np.diff(t) > 0)
    assert np.isin(x, [0, 1]).all()
    side = math.isqrt(x.shape[1])
    assert side * side == x.shape[1]
    expected = np.array([(a, b) for a in sorted(set(coords[:, 0]))
                         for b in sorted(set(coords[:, 1]))])
    assert np.array_equal(coords, expected)
    x = x.astype(np.int8).reshape(-1, side, side)
    harvest_raw = z.read(name.rsplit("/", 1)[0] + "/Harvest.csv")
    reader = csv.reader(io.StringIO(harvest_raw.decode("utf-8-sig")))
    hheader = next(reader)
    harvest = []
    for r in reader:
        if not r:
            continue
        assert len(r) == 4, "Expected observed four-column harvest payload"
        harvest.append((float(r[0]), r[1], int(float(r[2])), int(float(r[3]))))
    assert len(hheader) == 5 and hheader[-1] == "score"
    return t, x, coords, harvest


def ledger(t, x, q, pmax, phase, details=False, interval=1.0, birth_mask=None):
    """Deposit at phase+k*interval using the most recent observed board.

    Collapse/reset at the right endpoint of every inferred birth interval.
    With birth_mask=None, only observed 0->1 transitions are reset. At exact
    ties process the interval-end transition before
    depositing, so q always uses the latest observed state. The start height is
    zero at the first available snapshot (left-truncated observation window).
    """
    k0 = math.ceil((t[0] - phase) / interval)
    k1 = math.floor((t[-1] - phase) / interval)
    ticks = phase + np.arange(k0, k1 + 1) * interval
    ti = np.searchsorted(t, ticks, side="right") - 1
    flatx = x.reshape(len(t), -1)
    observed_births = np.diff(flatx, axis=0) == 1
    births = observed_births if birth_mask is None else birth_mask.reshape(len(t)-1,-1)
    bi = np.flatnonzero(np.any(births, axis=1)) + 1
    events = [(float(t[j]), 0, int(j)) for j in bi]
    events.extend((float(s), 1, int(j)) for s, j in zip(ticks, ti))
    # Read-out times are neither regeneration checks nor reset events.
    checkpoints = [s for s in (30., 60., 120., 180., 239.) if t[0] <= s <= t[-1]]
    if details:
        events.extend((s, 2, int(np.searchsorted(t, s, side="right") - 1)) for s in checkpoints)
    events.sort()
    height = np.zeros(flatx.shape[1])
    inflow = collapsed = 0.
    collapse_rows = []
    time_rows = []
    for time, kind, j in events:
        if kind == 0:
            ids = np.flatnonzero(births[j - 1])
            mass = height[ids].copy()
            collapsed += float(mass.sum())
            height[ids] = 0.
            if details:
                collapse_rows.extend({"interval_start":float(t[j-1]), "interval_end":time,
                                      "cell":int(i), "birth_observed_as_flip":int(observed_births[j-1,i]),
                                      "sand_at_interval_end_birth":float(v)} for i, v in zip(ids,mass))
        elif kind == 1:
            added = pmax * q[j].ravel()
            height += added
            inflow += float(added.sum())
        if details and (kind == 1 or kind == 2):
            live = q[j].ravel() > 0
            time_rows.append({"time": time, "readout": "tick" if kind == 1 else "checkpoint",
                              "N": int(flatx[j].sum()), "flow_potential": float(pmax * q[j].sum()),
                              "inflow": inflow, "collapsed": collapsed,
                              "height": float(height.sum()),
                              "stranded_height": float(height[~live].sum())})
    assert np.all(height[flatx[-1] == 1] < 1e-12)
    stranded = float(height[q[-1].ravel() == 0].sum())
    residual = float(height.sum())
    assert abs(inflow - collapsed - residual) < 1e-8
    return {"phase": float(phase), "tick_count": len(ticks), "inflow": inflow,
            "collapsed": collapsed, "height": residual, "stranded_height": stranded,
            "active_height": residual - stranded,
            "balance_error": inflow - collapsed - residual}, collapse_rows, time_rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data-dir", type=Path, default=Path(__file__).resolve().parent.parent / "cpr_empirical_sources")
    ap.add_argument("--outdir", type=Path, default=Path(__file__).resolve().parent / "results")
    ap.add_argument("--pmax", type=float, default=.01)
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    args.outdir.mkdir(parents=True, exist_ok=True)
    conditions = {(r["group"], r["subject"]): r for r in read_table(here / "conditions.csv")}
    flags = {(r["group"], r["subject"], int(r["round"])): r for r in read_table(here / "quality_flags.csv")}
    rows, collapse_rows, time_rows, phase_rows, loss_rows = [], [], [], [], []
    sources = []
    for group, filename in ARCHIVES.items():
        zpath = args.data_dir / filename
        sources.append({"filename": filename, "sha256": hashlib.sha256(zpath.read_bytes()).hexdigest(),
                        "size_bytes": zpath.stat().st_size})
        with ZipFile(zpath) as z:
            names = sorted(n for n in z.namelist() if "/03_rawdata/" in n and n.endswith("/TokenField.csv"))
            for no, name in enumerate(names):
                parts = name.split("/")
                subject = parts[-3].split("_", 1)[0]
                round_id = int(re.fullmatch(r"round(\d+)", parts[-2]).group(1))
                condition = conditions[group, subject]["condition"]
                qc = flags.get((group, subject, round_id), {}).get("decision", "include")
                key = {"group": group, "subject": subject, "round": round_id,
                       "condition": condition, "qc": qc, "trial": f"{group}_{subject}_r{round_id}"}
                t, x, coords, harvest = load_trial(z, name)
                n = moore_counts(x)
                degree = moore_counts(np.ones_like(x[0]))
                q = (1 - x) * n / degree
                flow = q.sum(axis=(1, 2))
                N = x.sum(axis=(1, 2))
                d = np.diff(x, axis=0)
                b = (d == 1).sum(axis=(1, 2))
                losses = (d == -1).sum(axis=(1, 2))
                # Independent event matching shows a saved board precedes
                # Harvest events with the identical logged TaskTime.
                counts = np.zeros((len(t)-1, x.shape[1]*x.shape[2]),dtype=np.int16)
                coordinate_index = {tuple(c):i for i,c in enumerate(coords)}
                for ht,_,hx,hy in harvest:
                    interval_id = int(np.searchsorted(t,ht,side="right")-1)
                    if 0 <= interval_id < len(t)-1:
                        counts[interval_id,coordinate_index[hx,hy]] += 1
                inferred_births = counts.reshape(d.shape) + d
                assert np.isin(inferred_births,[0,1]).all(), "Birth/harvest interval inconsistency"
                hw = int(counts.sum())
                balance_births = hw + int(N[-1]) - int(N[0])
                assert balance_births == int(inferred_births.sum())
                zero = np.flatnonzero(N == 0)
                r = dict(key, frames=len(t), board_side=x.shape[1], t_start=float(t[0]), t_end=float(t[-1]),
                         dt_median=float(np.median(np.diff(t))), N_start=int(N[0]), N_end=int(N[-1]),
                         observed_births=int(b.sum()), observed_losses=int(losses.sum()),
                         harvest_all=len(harvest), harvest_window=hw, balance_births=balance_births,
                         balance_minus_observed_births=balance_births-int(b.sum()),
                         first_zero=float(t[zero[0]]) if len(zero) else "",
                         exposure_integral=float(np.dot(flow[:-1], np.diff(t))),
                         continuous_inflow_proxy=float(args.pmax * np.dot(flow[:-1], np.diff(t))),
                         fixed8_continuous_proxy=float(args.pmax * np.dot(((1-x)*n).sum(axis=(1,2))[:-1]/8, np.diff(t))))
                # Isolated net losses: exact change in the observed-board function.
                il = np.flatnonzero((b == 0) & (losses == 1))
                delta = args.pmax * (flow[il+1] - flow[il])
                r.update(single_loss_frames=len(il), positive_loss_delta=int((delta > 1e-10).sum()),
                         negative_loss_delta=int((delta < -1e-10).sum()), neutral_loss_delta=int((abs(delta) <= 1e-10).sum()),
                         mean_single_loss_delta=float(delta.mean()) if len(delta) else "")
                for j, dv in zip(il, delta):
                    v = np.argwhere(d[j] == -1)[0]
                    vx, vy = map(int, v)
                    neighbors = [(a,c) for a in range(max(0,vx-1),min(x.shape[1],vx+2))
                                 for c in range(max(0,vy-1),min(x.shape[2],vy+2)) if (a,c)!=(vx,vy)]
                    predicted = args.pmax * (n[j,vx,vy]/degree[vx,vy]
                                             - sum((1-x[j,a,c])/degree[a,c] for a,c in neighbors))
                    assert abs(predicted-dv) < 1e-12
                    loss_rows.append(dict(key, time_observed=float(t[j+1]), neighbor_count=int(n[j,vx,vy]),
                                          degree=int(degree[vx,vy]), delta_flow=float(dv)))
                for phase in PHASES:
                    s, cr, tr = ledger(t,x,q,args.pmax,float(phase),details=phase==0,
                                       birth_mask=inferred_births.astype(bool))
                    phase_rows.append(dict(key, **s))
                    if phase == 0:
                        r.update({k:v for k,v in s.items() if k != "phase"})
                        collapse_rows.extend(dict(key, **c) for c in cr)
                        time_rows.extend(dict(key, **u) for u in tr)
                visible_only,_,_ = ledger(t,x,q,args.pmax,0.)
                r["observed_only_collapsed"] = visible_only["collapsed"]
                r["observed_only_height"] = visible_only["height"]
                r["hidden_reset_height_correction"] = r["height"]-visible_only["height"]
                vals = [a for a in phase_rows[-len(PHASES):]]
                for metric in ("inflow", "collapsed", "height"):
                    r[metric+"_phase_min"] = min(a[metric] for a in vals)
                    r[metric+"_phase_max"] = max(a[metric] for a in vals)
                r["inflow_phase_range_fraction"] = (r["inflow_phase_max"]-r["inflow_phase_min"])/r["inflow"] if r["inflow"] else ""
                for ct in (30,60,120,180,239):
                    if t[0] <= ct <= t[-1]:
                        j = int(np.searchsorted(t,ct,side="right")-1)
                        r[f"N_{ct}s"] = int(N[j])
                        r[f"flow_{ct}s"] = float(args.pmax*flow[j])
                rows.append(r)
                if (no+1)%40 == 0:
                    print(f"{group}: {no+1}/{len(names)} rounds processed", flush=True)
    write_csv(args.outdir / "round_sand.csv", rows)
    write_csv(args.outdir / "birth_sand.csv", collapse_rows)
    write_csv(args.outdir / "timecourse.csv", time_rows)
    write_csv(args.outdir / "phase_sensitivity.csv", phase_rows)
    write_csv(args.outdir / "isolated_loss.csv", loss_rows)
    metadata = {"pmax":args.pmax, "phases":PHASES.tolist(), "clock_period":1.0,
                "clock_type":"operational_fixed_grid_not_internal_coroutine_replay",
                "starting_height":0, "window":"first through last recorded board; harvest events in [first,last)",
                "collapse_rule":"reset all height at right endpoint of each inferred birth interval",
                "birth_intervals":"B_i,k=Harvest_i,[t_k,t_k+1)+x_i,k+1-x_i,k; all counts checked to be 0 or 1",
                "hidden_births":"included via interval balance; right-end reset is an operational approximation, not an observed exact birth time",
                "sources":sources, "round_count_all":len(rows),
                "round_count_main":sum(r["qc"] != "exclude" for r in rows),
                "largest_abs_balance_error":max(abs(r["balance_error"]) for r in rows)}
    (args.outdir/"method.json").write_text(json.dumps(metadata,ensure_ascii=False,indent=2)+"\n")
    print(json.dumps(metadata,ensure_ascii=False,indent=2),flush=True)


if __name__ == "__main__":
    main()
