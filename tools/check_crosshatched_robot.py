"""Independent integer checks for the cross-hatched and circular-arc extensions."""

from collections import Counter
import json


def small_rectangles(width, height):
    """Inspect all four corners in u=x+y, v=x-y coordinates."""
    vertices = {
        (u, v)
        for u in range(width + height + 1)
        for v in range(-height, width + 1)
        if 0 <= u + v <= 2 * width and 0 <= u - v <= 2 * height
    }
    counts = []
    for du, dv in [(1, 1), (1, 2), (2, 1)]:
        counts.append(sum(
            (u + du, v) in vertices and (u, v + dv) in vertices
            and (u + du, v + dv) in vertices
            for u, v in vertices
        ))
    return counts[0], counts[1] + counts[2]


def check_grids():
    observations = {}
    for width in range(1, 13):
        for height in range(width, 13):
            c2, c3 = small_rectangles(width, height)
            assert c2 == 2 * width * height - width - height
            assert c3 == 4 * (width - 1) * (height - 1)
            assert (c2, c3) not in observations
            observations[c2, c3] = width, height
    assert small_rectangles(1, 8) == (7, 0)
    assert small_rectangles(2, 3) == (7, 8)
    assert small_rectangles(2, 5) == (13, 16)
    assert small_rectangles(3, 3) == (12, 16)
    return {
        "boards": len(observations),
        "collision_on_c2": [[1, 8, 7, 0], [2, 3, 7, 8]],
        "collision_on_c3": [[2, 5, 13, 16], [3, 3, 12, 16]],
    }


def check_ninth_root_walks():
    # Powers of z in the basis 1,z,...,z^5, using z^6 = -z^3 - 1.
    powers = [(1, 0, 0, 0, 0, 0)]
    for _ in range(9):
        a, b, c, d, e, f = powers[-1]
        powers.append((-f, a, b, c - f, d, e))
    assert powers[9] == powers[0]
    closed = Counter()
    visited = 0
    zero = (0,) * 6

    def visit(heading, displacement, length):
        nonlocal visited
        if length:
            visited += 1
            if displacement == zero:
                assert heading == 0
                closed[length] += 1
        if length == 18:
            return
        for turn in (-1, 1):
            new_heading = (heading + turn) % 9
            edge = heading if turn == 1 else new_heading
            moved = tuple(x + y for x, y in zip(displacement, powers[edge]))
            visit(new_heading, moved, length + 1)

    visit(0, zero, 0)
    assert visited == 524286 and closed == {9: 2, 15: 10, 18: 20}
    return {"order": 9, "max_length": 18, "words": visited, "closed": dict(sorted(closed.items()))}


if __name__ == "__main__":
    print(json.dumps({"grid": check_grids(), "robot": check_ninth_root_walks()}, indent=2))
