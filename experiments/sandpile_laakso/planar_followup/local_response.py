"""Compare one-grain response around sibling sources. Run with Python and NumPy."""

from collections import Counter
import json

from planar_sandpile import as_counter, drive, parallel_sources, source_partition


SOURCE_X = (-17, -15, -9, -7, 7, 9, 15, 17)
SOURCE_IDS = {(x, 0): label for x, label in zip(SOURCE_X, "ABCDEFGH")}
OFFSETS = ((0, 0), (-1, 0), (1, 0), (0, -1), (0, 1))


def measure(mass, left_x, right_x):
    deposits = {s: mass for s in SOURCE_IDS}
    heights_array, odometer_array, _, base_flux = parallel_sources(deposits)
    baseline = as_counter(heights_array)
    u = as_counter(odometer_array)

    # Fully independent baseline: add sources in reverse order and stabilize by FIFO.
    sequential, total = Counter(), Counter()
    for p in reversed(deposits):
        total.update(drive(sequential, mass, lifo=False, source=p))
    assert total == u and sequential == baseline

    # The 2D component born at this merge consists exactly of this pair.
    threshold = min(u[(x, 0)] for x in range(left_x, right_x + 1))
    ids = SOURCE_IDS[(left_x, 0)] + SOURCE_IDS[(right_x, 0)]
    after_merge = source_partition(u, threshold, SOURCE_IDS)
    before_merge = source_partition(u, threshold + 1, SOURCE_IDS)
    assert ids in after_merge and all(id_ in before_merge for id_ in ids)
    trials = []
    for x in (left_x, right_x):
        source = (x, 0)
        next_state = baseline.copy()
        inc = drive(next_state, 1, lifo=True, source=source)
        assert sum(next_state.values()) == sum(baseline.values()) + 1
        # Independent check: stabilize every input simultaneously from zero.
        full_drive = deposits.copy()
        full_drive[source] += 1
        final_h, final_u, _, final_flux = parallel_sources(full_drive)
        assert final_flux == 0 and u + inc == as_counter(final_u)
        assert next_state == as_counter(final_h)
        sites = [(x + dx, dy) for dx, dy in OFFSETS]
        trials.append({
            "source": [x, 0],
            "heights_before": [baseline[p] for p in sites],
            "extra_firings": [inc[p] for p in sites],
            "all_sites_extra_firings": sum(inc.values()),
            "boundary_flux": final_flux,
        })
    assert trials[0]["extra_firings"] != trials[1]["extra_firings"]
    return {
        "grains_per_source": mass,
        "base_boundary_flux": base_flux,
        "tested_pair": ids, "merge_level": threshold,
        "source_partition_at_merge": after_merge,
        "source_partition_one_above_merge": before_merge,
        "separate_drives_from_same_baseline": trials,
    }


def main():
    rows = [measure(256, -17, -15), measure(260, -9, -7), measure(609, -17, -15)]
    cross = rows[-1]["separate_drives_from_same_baseline"]
    assert cross[0]["heights_before"] == cross[1]["heights_before"] == [3] * 5
    assert sorted(cross[0]["extra_firings"][1:]) != sorted(cross[1]["extra_firings"][1:])
    print(json.dumps({
        "source_x_at_y_zero": SOURCE_X,
        "offset_order": OFFSETS,
        "protocol": ["zero background; eight equal deposits and full stabilization",
                     "clone baseline, add one grain at each tested sibling in its separate run",
                     "LIFO perturbation verified by fresh whole-input parallel stabilization",
                     "same sibling merge certified by 2D excursion components at k and k+1",
                     "wired parallel runs checked zero flux, empty outer ring, and exact Laplacian"],
        "rows": rows,
    }, indent=2))


if __name__ == "__main__":
    main()
