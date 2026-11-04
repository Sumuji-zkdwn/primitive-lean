"""An explicit, optional border-counter invariance hypothesis.

This is a heuristic, not proof that the excluded pixels are causally irrelevant.
Raw observations and the unmasked ablation remain available for evaluation.
"""
from collections import Counter, deque

from .perception import Action, Observation


class CounterRepresentation:
    def __init__(self, enabled: bool = True) -> None:
        self.enabled = enabled
        self.rows_by_level: dict[int, set[int]] = {}
        self.window: deque[tuple[Observation, Action | None]] = deque(maxlen=32)

    def update(self, obs: Observation, action: Action | None) -> bool:
        if not self.enabled:
            return False
        if (action is None or obs.terminal or
                (self.window and self.window[-1][0].levels != obs.levels)):
            self.window.clear()
        self.window.append((obs, action))
        if len(self.window) < 32 or obs.levels in self.rows_by_level:
            return False
        if len({a for _, a in self.window if a is not None}) < 3:
            return False
        frames = [o.grid for o, _ in self.window]
        height, width = len(obs.grid), len(obs.grid[0])
        if height < 32 or width < 32 or any(len(f) != height for f in frames):
            return False
        candidates = list(range(4)) + list(range(height-4, height))
        excluded = set()
        for y in candidates:
            rows = [frame[y] for frame in frames]
            if any(len(row) != width for row in rows):
                continue
            changes = sum(a != b for a, b in zip(rows, rows[1:]))
            if changes < 8:
                continue
            # Judge only varying pixels: static labels can sit beside a counter.
            varying_x = [x for x in range(width) if len({row[x] for row in rows}) > 1]
            samples = [[row[x] for x in varying_x] for row in rows]
            if max(1 + sum(a != b for a, b in zip(row, row[1:])) for row in samples) > 4:
                continue
            counts = [Counter(row) for row in rows]
            colors = set(c for row in rows for c in row)
            varying = []
            monotonic = True
            for color in colors:
                seq = [c[color] for c in counts]
                diffs = [b-a for a,b in zip(seq, seq[1:]) if a != b]
                if diffs:
                    varying.append(color)
                    monotonic &= all(d > 0 for d in diffs) or all(d < 0 for d in diffs)
            if monotonic and len(varying) == 2:
                excluded.add(y)
        if excluded:
            self.rows_by_level[obs.levels] = excluded
            return True
        return False

    def transform(self, obs: Observation) -> Observation:
        rows = self.rows_by_level.get(obs.levels, set())
        if not rows:
            return obs
        return Observation(tuple(tuple(0 for _ in row) if y in rows else row
                                 for y, row in enumerate(obs.grid)),
                           obs.available, obs.levels, obs.status)
