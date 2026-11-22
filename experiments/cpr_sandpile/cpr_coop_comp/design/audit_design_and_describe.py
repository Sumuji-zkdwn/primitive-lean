"""Audit the Coop/Comp design and describe original CPR outcomes.

The primary archive is read without extracting participant identifiers. The
two participant columns are inspected only for label format/collisions; those
labels are never written. Round outcomes are averaged within numeric pair ID,
then pair means are weighted equally. No significance or causal test is run.
"""
from __future__ import annotations

import collections
import csv
import hashlib
import importlib.util
import io
import json
import re
from pathlib import Path
from xml.etree import ElementTree as ET
from zipfile import ZipFile

import numpy as np
import openpyxl


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
ARCHIVE = ROOT / "cpr_empirical_sources" / "02_expCPR_2player(1).zip"
METRICS = (
    "harvest_all", "harvest_window", "balance_births", "observed_birth_flips", "N_end", "N_60",
    "N_120", "N_180", "R_60", "mean_N_timeweighted", "sustained_zero_by60", "sustained_zero_observed",
    "terminal_zero", "nonzero_time_capped239", "harvest_first60",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_csv(path):
    with Path(path).open(encoding="utf-8-sig", newline="") as f:
        return list(csv.DictReader(f))


def write_csv(path, rows):
    if not rows:
        return
    keys = list(dict.fromkeys(key for row in rows for key in row))
    with Path(path).open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, keys)
        writer.writeheader()
        writer.writerows(rows)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def docx_paragraphs(raw):
    with ZipFile(io.BytesIO(raw)) as z:
        tree = ET.fromstring(z.read("word/document.xml"))
    ns = {"w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main"}
    return [{"paragraph": i, "text": "".join(e.text or "" for e in p.findall(".//w:t", ns))}
            for i, p in enumerate(tree.findall(".//w:p", ns))]


def sources_and_design(z, conditions):
    instruction_sources = []
    for member in sorted(n for n in z.namelist() if "/02_instruction/" in n and n.endswith(".docx")):
        raw = z.read(member)
        paragraphs = docx_paragraphs(raw)
        full = "\n".join(p["text"] for p in paragraphs)
        if "合計スコアが２００点未満" in full:
            condition = "Coop"
        elif "個人スコアが１００点未満" in full:
            condition = "Comp"
        else:
            raise ValueError("Unrecognized instruction document")
        output_name = f"instruction_{condition.lower()}.txt"
        (HERE / output_name).write_text("\n".join(f"[paragraph {p['paragraph']}] {p['text']}" for p in paragraphs if p["text"].strip()) + "\n", encoding="utf-8")
        instruction_sources.append({"condition": condition, "archive_member": member,
                                    "sha256": sha256(raw), "extracted_text": output_name,
                                    "relevant_paragraphs": [p for p in paragraphs if any(word in p["text"] for word in
                                        ("相手のスコア", "合計スコアが高得点", "２００点未満", "１００点未満", "240秒", "会話や相談", "ラウンドごとに休憩"))]})
    require(set(s["condition"] for s in instruction_sources) == {"Coop", "Comp"}, "Missing instructions")
    workbook_members = [n for n in z.namelist() if n.endswith("CPRtask_condition_2player.xlsx")]
    workbook_hashes = {n: sha256(z.read(n)) for n in workbook_members}
    require(len(set(workbook_hashes.values())) == 1, "Condition workbook copies differ")
    member = next(n for n in workbook_members if "/03_rawdata/" in n)
    workbook = openpyxl.load_workbook(io.BytesIO(z.read(member)), read_only=True, data_only=True)
    rows = list(workbook.active.iter_rows(values_only=True))
    require(rows[0][:7] == ("ID", "Player1", "Player2", "Date", "Condition", "TokenNum", "BoardSize"), "Unexpected workbook columns")
    anonymous_conditions = []
    participant_labels = collections.defaultdict(list)
    label_formats = collections.Counter()
    for row in rows[1:]:
        if row[0] is None:
            continue
        pair = f"{int(row[0]):02d}"
        condition = row[4]
        require(conditions[pair]["condition"] == condition, "Workbook/conditions.csv mismatch")
        require(int(conditions[pair]["planned_initial_tokens"]) == row[5] and int(conditions[pair]["board_size"]) == row[6], "Workbook board parameters differ")
        anonymous_conditions.append({"pair": pair, "condition": condition, "planned_initial_tokens": int(row[5]),
                                     "board_side": int(row[6]), "note": row[7] or ""})
        for slot in (1, 2):
            label = str(row[slot]).strip()
            label_formats[(len(label), bool(re.fullmatch("[A-Za-z]+", label))) ] += 1
            participant_labels[label].append({"pair": pair, "slot": slot, "condition": condition})
    collisions = [occurrences for occurrences in participant_labels.values() if len(occurrences) > 1]
    # The repeated raw strings are deliberately omitted, even from metadata.
    participants = {
        "slots": sum(len(v) for v in participant_labels.values()), "distinct_label_strings": len(participant_labels),
        "label_formats": [{"length": key[0], "alphabetic_ascii": key[1], "slots": count} for key, count in label_formats.items()],
        "n_repeated_label_strings": len(collisions), "anonymous_collisions": collisions,
        "interpretation": "Every label is two ASCII letters. Repeated initials may be the same person or different people. Neither 40 unique people nor 32 people is established.",
        "independence": "Pair-level aggregation avoids independent treatment of repeated rounds, but independence across pair IDs remains unverified because participant identities are not unique in this file.",
    }
    return {
        "comparison_design": "between_pair_conditions_with_repeated_rounds_within_each_pair",
        "condition_assignment": "one fixed condition per pair; odd numeric IDs Comp, even numeric IDs Coop",
        "condition_switching_within_pair": False,
        "randomization": "Not documented in the inspected instruction documents or condition workbook. Odd/even IDs do not establish allocation procedure.",
        "round_order": "The instruction specifies eight test rounds with breaks; raw folders are numbered round1 through round8. No within-pair Coop/Comp crossover is recorded.",
        "instruction_sources": instruction_sources, "condition_workbook_sources": workbook_hashes,
        "anonymous_conditions": anonymous_conditions, "participant_label_audit": participants,
        "common_instruction": {"seconds_per_round": 240, "test_rounds": 8, "practice_before_test": True,
                               "breaks_between_rounds": True, "communication": "Conversation and consultation prohibited until experiment end",
                               "regeneration_information": "Both state that new tokens can appear in empty cells; neither describes the neighborhood probability rule in the extracted text."},
        "condition_manipulation": {
            "Coop": {"objective": "Maximize the sum of the two participants' scores", "threshold": "A round total below 200 becomes zero", "display_text": "Total score"},
            "Comp": {"objective": "Make one's own score exceed the other participant's score", "threshold": "An individual round score below 100 becomes zero", "display_text": "Individual scores"},
            "caution": "The condition changes the stated goal, score presentation and threshold rule; the raw harvest counts below are not threshold-adjusted official scores.",
        },
    }


def describe(values):
    a = np.asarray(values, dtype=float)
    return {"n_pairs": len(a), "mean": float(a.mean()), "sd_between_pair_means": float(a.std(ddof=1)),
            "median": float(np.median(a)), "min": float(a.min()), "max": float(a.max()),
            "p25": float(np.quantile(a, .25)), "p75": float(np.quantile(a, .75))}


def main():
    HERE.mkdir(parents=True, exist_ok=True)
    analyzer_path = ROOT / "cpr_empirical" / "analyze_sand.py"
    spec = importlib.util.spec_from_file_location("cpr_design_original_analyzer", analyzer_path)
    analyzer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(analyzer)
    condition_path = ROOT / "cpr_empirical" / "conditions.csv"
    flag_path = ROOT / "cpr_empirical" / "quality_flags.csv"
    reference_path = ROOT / "cpr_empirical" / "results" / "round_sand.csv"
    conditions = {r["subject"]: r for r in read_csv(condition_path) if r["group"] == "two"}
    flags = {(r["subject"], int(r["round"])): r for r in read_csv(flag_path) if r["group"] == "two"}
    reference = {r["trial"]: r for r in read_csv(reference_path) if r["group"] == "two"}
    all_rows, member_rounds = [], collections.defaultdict(list)
    max_errors = collections.defaultdict(float)
    with ZipFile(ARCHIVE) as z:
        design = sources_and_design(z, conditions)
        names = sorted(n for n in z.namelist() if "/03_rawdata/" in n and n.endswith("/TokenField.csv"))
        for name in names:
            parts = name.split("/")
            pair = parts[-3].split("_", 1)[0]
            round_no = int(re.fullmatch(r"round(\d+)", parts[-2]).group(1))
            member_rounds[pair].append(round_no)
            trial = f"two_{pair}_r{round_no}"
            qc = flags.get((pair, round_no), {}).get("decision", "include")
            t, x, _, harvest = analyzer.load_trial(z, name)
            n = x.sum(axis=(1, 2))
            require(x.shape[1:] == (19, 19) and n[0] == 90, "Initial state differs from design table")
            htimes = np.asarray([v[0] for v in harvest])
            hw = int(np.count_nonzero((htimes >= t[0]) & (htimes < t[-1])))
            births = hw + int(n[-1]) - int(n[0])
            observed = int((np.diff(x, axis=0) == 1).sum())
            zero_ids = np.flatnonzero(n == 0)
            first_zero = float(t[zero_ids[0]]) if len(zero_ids) else None
            if len(zero_ids):
                require(bool(np.all(n[zero_ids[0]:] == 0)), "Resource count becomes positive after zero")
            sustained = first_zero is not None and t[-1] - first_zero >= 10.
            snap = {sec: int(n[np.searchsorted(t, sec, side="right") - 1]) for sec in (30, 60, 120, 180, 239)}
            require(t[0] < 1 and t[-1] > 239, "239-second comparison horizon not observed")
            record = {"trial": trial, "pair": pair, "condition": conditions[pair]["condition"], "round": round_no,
                      "qc": qc, "frames": len(t), "t_start": float(t[0]), "t_end": float(t[-1]),
                      "harvest_all": len(harvest), "harvest_window": hw, "balance_births": births,
                      "harvest_before_first_frame": int(np.count_nonzero(htimes < t[0])),
                      "harvest_at_or_after_last_frame": int(np.count_nonzero(htimes >= t[-1])),
                      "observed_birth_flips": observed, "N_start": int(n[0]), "N_end": int(n[-1]),
                      **{f"N_{sec}": val for sec, val in snap.items()}, "R_60": snap[60] / 90.,
                      "mean_N_timeweighted": float(np.dot(n[:-1], np.diff(t)) / (t[-1] - t[0])),
                      "first_observed_zero_s": first_zero,
                      "sustained_zero_by60": int(sustained and first_zero <= 60.),
                      "sustained_zero_observed": int(sustained), "terminal_zero": int(n[-1] == 0),
                      "nonzero_time_capped239": min(first_zero, 239.) if first_zero is not None else 239.,
                      "harvest_first60": int(np.count_nonzero((htimes >= t[0]) & (htimes < 60.)))}
            for ours, previous in (("harvest_all", "harvest_all"), ("harvest_window", "harvest_window"),
                                   ("balance_births", "balance_births"), ("observed_birth_flips", "observed_births"),
                                   ("N_end", "N_end"), ("N_60", "N_60s"), ("N_120", "N_120s"), ("N_180", "N_180s")):
                error = abs(record[ours] - float(reference[trial][previous]))
                max_errors[ours] = max(max_errors[ours], error)
                require(error == 0, f"Raw/previous summary mismatch: {trial}, {ours}")
            previous_zero = float(reference[trial]["first_zero"]) if reference[trial]["first_zero"] else None
            require(previous_zero == first_zero, "First-zero time differs from previous ledger")
            all_rows.append(record)
    require(len(all_rows) == 159 and len(member_rounds) == 20, "Unexpected raw sample")
    main_rows = [r for r in all_rows if r["qc"] != "exclude"]
    require(len(main_rows) == 157, "Unexpected main sample")
    pair_rows = []
    for pair, rounds in sorted(member_rounds.items()):
        rr = [r for r in main_rows if r["pair"] == pair]
        pair_row = {"pair": pair, "condition": conditions[pair]["condition"], "n_raw_rounds": len(rounds),
                    "n_valid_rounds": len(rr), "available_rounds": " ".join(map(str, sorted(rounds))),
                    "analyzed_rounds": " ".join(str(r["round"]) for r in rr)}
        for metric in METRICS:
            pair_row[metric] = float(np.mean([r[metric] for r in rr]))
        pair_rows.append(pair_row)
    condition_records = []
    for condition in ("Coop", "Comp"):
        pp = [r for r in pair_rows if r["condition"] == condition]
        rr = [r for r in main_rows if r["condition"] == condition]
        result = {"condition": condition, "n_pairs": len(pp), "n_raw_rounds": sum(r["n_raw_rounds"] for r in pp),
                  "n_analyzed_rounds": len(rr), "pair_ids": [r["pair"] for r in pp],
                  "pair_equal_metrics": {metric: describe([p[metric] for p in pp]) for metric in METRICS},
                  "pooled_round_counts": {metric: int(sum(r[metric] for r in rr)) for metric in
                                           ("sustained_zero_by60", "sustained_zero_observed", "terminal_zero")}}
        condition_records.append(result)
    by_condition = {r["condition"]: r for r in condition_records}
    differences = [{"metric": metric,
                    "Coop_pair_equal_mean": by_condition["Coop"]["pair_equal_metrics"][metric]["mean"],
                    "Comp_pair_equal_mean": by_condition["Comp"]["pair_equal_metrics"][metric]["mean"],
                    "Coop_minus_Comp": by_condition["Coop"]["pair_equal_metrics"][metric]["mean"] - by_condition["Comp"]["pair_equal_metrics"][metric]["mean"]}
                   for metric in METRICS]
    round_rows = []
    for condition in ("Coop", "Comp"):
        for round_no in range(1, 9):
            rr = [r for r in main_rows if r["condition"] == condition and r["round"] == round_no]
            round_rows.append({"condition": condition, "round": round_no, "n_pairs": len(rr),
                               **{metric: float(np.mean([r[metric] for r in rr])) for metric in METRICS}})
    quality = {"planned_pairs": 20, "planned_rounds": 160, "raw_rounds": 159, "main_rounds": 157,
               "missing": [{"pair": "19", "condition": "Comp", "round": 8, "reason": "folder absent"}],
               "excluded": [{"pair": "02", "condition": "Coop", "round": r, "reason": "controller problem and offline score NA"} for r in (7, 8)],
               "retained_review": [{"pair": "20", "condition": "Coop", "round": r, "reason": "interruption between rounds 1 and 2"} for r in (1, 2)]}
    report = {"design": design, "quality": quality, "conditions": condition_records, "differences": differences,
              "definitions": {
                  "unit": "Numeric pair ID. Mean available valid rounds per pair, then give the ten pair means equal weight within condition.",
                  "independence": "No assumption of unique participants is established; repeated two-letter labels leave possible cross-pair dependence unresolved.",
                  "harvest_all": "Number of rows in the original Harvest.csv, before any score thresholding",
                  "harvest_window": "Harvest events in [first TokenField timestamp, last TokenField timestamp)",
                  "first60_time_origin": "Logged TaskTime measured from t=0. The cutoff is the absolute timestamp 60.0 seconds, not first_field_time+60.",
                  "harvest_first60": "Harvest events with first_field_time <= rt < 60.0 in the original logged TaskTime; the lower limit is the first observed board.",
                  "balance_births": "Harvest_window + N_end - N_start; reconstructed count, including births hidden between saved frames",
                  "observed_birth_flips": "Visible 0->1 changes between consecutive saved boards; distinct from reconstructed total births",
                  "N_times": "Latest saved board no later than the named second, without interpolation",
                  "first_observed_zero": "First saved board with zero tokens; underlying event time is interval censored",
                  "sustained_zero": "Zero continuously to the end for ten or more logged seconds; raw data verified to remain zero after first zero",
                  "nonzero_time_capped239": "min(first observed zero time,239); 239 if not zero by then. This handles nondepleted trials without averaging only failures.",
                  "mean_N_timeweighted": "Left-step integral of observed total tokens divided by observed duration",
                  "round_order": "Folder-labelled rounds 1..8, matching the eight-round instruction; not inferred wall-clock times",
                  "anonymization": "Only numeric pair IDs and player-slot numbers identify membership in the output. The original two-letter participant strings and workbook dates are not written.",
                  "inference": "Descriptive only. No p-values, confidence intervals, randomized-allocation claim, or causal effect is produced here.",
              },
              "validation": {"raw_reference_differences": dict(max_errors), "zero_is_absorbing_in_all_raw_rounds": True,
                             "board_side_all_rounds": 19, "initial_tokens_all_rounds": 90},
              "source_hashes": {"archive": sha256(ARCHIVE.read_bytes()), "conditions_csv": sha256(condition_path.read_bytes()),
                                "quality_flags_csv": sha256(flag_path.read_bytes()), "round_sand_csv": sha256(reference_path.read_bytes()),
                                "analysis_code": sha256(Path(__file__).read_bytes()), "raw_loader_code": sha256(analyzer_path.read_bytes())}}
    write_csv(HERE / "round_metrics_all159.csv", all_rows)
    write_csv(HERE / "round_metrics_main157.csv", main_rows)
    write_csv(HERE / "pair_means.csv", pair_rows)
    write_csv(HERE / "condition_differences.csv", differences)
    write_csv(HERE / "round_order_descriptive.csv", round_rows)
    write_csv(HERE / "anonymous_condition_table.csv", design["anonymous_conditions"])
    (HERE / "design_and_outcomes.json").write_text(json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps({"design": design["comparison_design"], "quality": quality, "differences": differences,
                      "participant_label_audit": design["participant_label_audit"], "validation": report["validation"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
