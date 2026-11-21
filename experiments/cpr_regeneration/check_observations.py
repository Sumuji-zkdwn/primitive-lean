"""Check logged CPR board changes. Usage: python3 check_observations.py ONE.zip TWO.zip

Input ZIPs are opened read-only. Outputs aggregate counts by default.
An optional local quality table supplies exclusions and a flag enables witness details.
"""

import argparse
import csv
import hashlib
import json
from bisect import bisect_left
from collections import Counter
from pathlib import Path
from zipfile import ZipFile

if __package__:
    from .verify_model import Board
else:
    from verify_model import Board


def sites_in(bits):
    while bits:
        low = bits & -bits
        yield low.bit_length() - 1
        bits ^= low


def summarize_field(board, state, units):
    sand = board.sand(state)
    return sum(sand), sum(w * n for w, n in zip(units, sand))


def sign_label(value):
    if value > 0:
        return "increase"
    if value < 0:
        return "decrease"
    return "unchanged"


def centered_coordinates(i, side):
    x, y = divmod(i, side)
    return [x - side // 2, y - side // 2]


def birth_order_possible(board, state, ordered_births):
    for i in ordered_births:
        if not state & board.masks[i]:
            return False
        state |= 1 << i
    return True


def observed_boards(stream, board):
    radius = board.side // 2
    coords = range(-radius, radius + 1)
    header = stream.readline().decode("utf-8-sig").rstrip("\r\n").split(",")
    if header != ["time"] + [f"token_{x}_{y}" for x in coords for y in coords]:
        raise ValueError("unexpected board header; coordinates must match the scan order")
    commas = b"," * (board.size - 1)
    for line in stream:
        raw_time, payload = line.rstrip(b"\r\n").split(b",", 1)
        digits = payload[::2]
        if (len(digits) != board.size or payload[1::2] != commas or
                digits.count(b"0") + digits.count(b"1") != board.size):
            raise ValueError("expected a complete binary board")
        yield float(raw_time), int(digits[::-1], 2)


def inspect_archive(path, side, excluded, *, include_witnesses=False):
    board = Board(side)
    units = board.units("degree")
    counts = Counter()
    change_signs = {rule: Counter() for rule in ("fixed8", "degree")}
    sign_cross_table = Counter()
    order_support = Counter()
    witnesses = []
    subjects = set()
    cut_min, cut_max = None, None
    max_interval = 0.0
    seen_rounds = set()
    with ZipFile(path) as archive:
        fields = sorted(n for n in archive.namelist()
                        if "/03_rawdata/" in n and n.endswith("/TokenField.csv")
                        and "__MACOSX/" not in n)
        for name in fields:
            parts = name.split("/")
            subject = int(parts[-3].split("_", 1)[0])
            number = int(parts[-2].removeprefix("round"))
            key = (subject, number)
            if key in seen_rounds:
                raise ValueError("duplicate subject and round in raw input")
            seen_rounds.add(key)
            if key in excluded:
                continue
            subjects.add(subject)
            counts["rounds"] += 1
            harvest_name = name.rsplit("/", 1)[0] + "/Harvest.csv"
            with archive.open(harvest_name) as harvest:
                if harvest.readline().decode("utf-8-sig").split(",")[0] != "rt":
                    raise ValueError("unexpected harvest header")
                harvest_times = sorted(float(row.split(b",", 1)[0]) for row in harvest)
            saw_zero = False
            came_back = False
            prev = None
            prev_time = None
            with archive.open(name) as stream:
                for t, state in observed_boards(stream, board):
                    counts["snapshots"] += 1
                    if prev_time is not None:
                        if t <= prev_time:
                            raise ValueError("snapshot times must be increasing")
                        max_interval = max(max_interval, t - prev_time)
                    if saw_zero and state:
                        came_back = True
                    if state == 0:
                        saw_zero = True
                    if prev is None or prev != state:
                        total = summarize_field(board, state, units)
                        if state.bit_count() == 20:
                            cut = total[0]
                            cut_min = cut if cut_min is None else min(cut_min, cut)
                            cut_max = cut if cut_max is None else max(cut_max, cut)
                        if prev is not None:
                            births = state & ~prev
                            losses = prev & ~state
                            counts["visible_new_cells"] += births.bit_count()
                            if losses.bit_count() == 1 and not births:
                                i = losses.bit_length() - 1
                                n = board.count(prev, i)
                                actual = (total[0] - prev_total[0], total[1] - prev_total[1])
                                neighbors = board.neighbors[i]
                                empty_weights = sum(units[j] for j in neighbors if not prev & (1 << j))
                                predicted = (2 * n - len(neighbors), n * units[i] - empty_weights)
                                if actual != predicted:
                                    raise AssertionError("observed field difference disagrees with local formula")
                                counts["single_loss_intervals"] += 1
                                for rule, delta in zip(("fixed8", "degree"), actual):
                                    change_signs[rule][sign_label(delta)] += 1
                                sign_cross_table[sign_label(actual[0]) + "_to_" + sign_label(actual[1])] += 1
                            if births and not losses:
                                # Drop even endpoint-tied harvests to avoid timestamp ambiguity.
                                k = bisect_left(harvest_times, prev_time)
                                if k == len(harvest_times) or harvest_times[k] > t:
                                    added = list(sites_in(births))
                                    forward = birth_order_possible(board, prev, added)
                                    reverse = birth_order_possible(board, prev, reversed(added))
                                    frozen = all(prev & board.masks[i] for i in added)
                                    counts["birth_intervals_without_loss_or_logged_harvest"] += 1
                                    counts["ineligible_on_previous_snapshot_intervals"] += int(not frozen)
                                    if not frozen and include_witnesses:
                                        witnesses.append({
                                            "subject_or_pair_number": subject, "round": number,
                                            "interval_seconds": [prev_time, t],
                                            "new_cells": [centered_coordinates(i, side) for i in added],
                                            "new_cells_without_old_neighbor": [
                                                centered_coordinates(i, side)
                                                for i in added if not prev & board.masks[i]
                                            ],
                                            "old_neighbors_in_same_order_as_new_cells": [
                                                [centered_coordinates(j, side) for j in board.neighbors[i]
                                                 if prev & (1 << j)] for i in added
                                            ],
                                            "forward_compatible": forward, "reverse_compatible": reverse,
                                        })
                                    if not frozen:
                                        order_support[{(True, False): "forward_only",
                                                       (False, True): "reverse_only",
                                                       (True, True): "both",
                                                       (False, False): "neither"}[forward, reverse]] += 1
                        prev_total = total
                    prev, prev_time = state, t
            if prev is None:
                raise ValueError("round has no snapshots")
            counts["rounds_reaching_zero"] += int(saw_zero)
            counts["rounds_with_later_nonempty_snapshot"] += int(came_back)
    if not fields or not excluded <= seen_rounds:
        raise ValueError("raw archive layout or quality-exclusion IDs do not match")
    return {
        "archive_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "side": side, "subjects_or_pairs": len(subjects), "raw_rounds": len(seen_rounds),
        "excluded_rounds": len(excluded), "counts": dict(counts),
        "maximum_snapshot_interval_seconds": round(max_interval, 7),
        "cut_range_when_20_occupied": [cut_min, cut_max],
        "observed_single_loss_frame_change_signs": change_signs,
        "single_loss_change_sign_fixed8_to_degree": sign_cross_table,
        "order_support_in_ineligible_intervals": {
            key: order_support[key] for key in ("forward_only", "reverse_only", "both", "neither")
        },
        **({"witnesses": witnesses} if include_witnesses else {}),
    }


def quality_exclusions(path):
    exclusions = {"one": set(), "two": set()}
    if path is not None:
        with path.open(encoding="utf-8-sig", newline="") as stream:
            for row in csv.DictReader(stream):
                if row["decision"] == "exclude":
                    exclusions[row["group"]].add((int(row["subject"]), int(row["round"])))
    return exclusions


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("one_player_zip", type=Path)
    parser.add_argument("two_player_zip", type=Path)
    parser.add_argument("--quality-flags", type=Path,
                        help="local CSV with group (one/two), subject, round, decision")
    parser.add_argument("--witnesses", action="store_true", help="include individual intervals in local output")
    args = parser.parse_args()
    excluded = quality_exclusions(args.quality_flags)
    results = {"one_player": inspect_archive(args.one_player_zip, 13, excluded["one"],
                                             include_witnesses=args.witnesses),
               "two_player": inspect_archive(args.two_player_zip, 19, excluded["two"],
                                             include_witnesses=args.witnesses)}
    print(json.dumps(results, indent=2))
