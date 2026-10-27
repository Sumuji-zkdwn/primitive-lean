from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from hashlib import blake2b
from typing import Any

Grid = tuple[tuple[int, ...], ...]


@dataclass(frozen=True, order=True)
class Action:
    code: int
    x: int = -1
    y: int = -1

    def __post_init__(self) -> None:
        if not 0 <= self.code <= 7:
            raise ValueError("Action code must be between 0 and 7")
        if self.code == 6:
            if not (0 <= self.x < 64 and 0 <= self.y < 64):
                raise ValueError("Click coordinates must lie in [0, 63]")
        elif (self.x, self.y) != (-1, -1):
            raise ValueError("Only ACTION6 accepts coordinates")

    @property
    def data(self) -> dict[str, int]:
        return {"x": self.x, "y": self.y} if self.code == 6 else {}

    def token(self) -> str:
        return f"{self.code}:{self.x}:{self.y}"

    @classmethod
    def parse(cls, token: str) -> Action:
        return cls(*map(int, token.split(":")))


@dataclass(frozen=True)
class Observation:
    grid: Grid
    available: tuple[int, ...]
    levels: int = 0
    status: str = "NOT_FINISHED"

    def __post_init__(self) -> None:
        if not self.grid or not self.grid[0]:
            raise ValueError("Empty frame")
        if len(self.grid) > 64 or len(self.grid[0]) > 64:
            raise ValueError("Expected at most 64 by 64 pixels")
        if any(len(row) != len(self.grid[0]) for row in self.grid):
            raise ValueError("Ragged frame")
        if any(not 0 <= c <= 15 for row in self.grid for c in row):
            raise ValueError("Expected palette indices from 0 to 15")
        if any(c not in range(8) for c in self.available):
            raise ValueError("Unsupported available action")

    @classmethod
    def from_sdk(cls, raw: Any) -> Observation:
        if raw is None or len(raw.frame) == 0:
            raise ValueError("SDK returned no frame")
        # The SDK may return intermediate animation frames. Use the final frame.
        return cls(
            tuple(tuple(map(int, row)) for row in raw.frame[-1]),
            tuple(sorted(set(map(int, raw.available_actions)))),
            int(raw.levels_completed),
            raw.state.name,
        )

    @property
    def terminal(self) -> bool:
        return self.status in {"WIN", "GAME_OVER"}

    @property
    def key(self) -> str:
        header = repr((len(self.grid), len(self.grid[0]), self.available,
                       self.levels, self.status)).encode()
        pixels = bytes(c for row in self.grid for c in row)
        return blake2b(header + b"|" + pixels, digest_size=16).hexdigest()


@dataclass(frozen=True)
class Component:
    color: int
    pixels: tuple[tuple[int, int], ...]

    @property
    def center(self) -> tuple[int, int]:
        # Select an actual component pixel, including for concave/hollow objects.
        n = len(self.pixels)
        sx = sum(p[0] for p in self.pixels)
        sy = sum(p[1] for p in self.pixels)
        return min(self.pixels, key=lambda p: (n*p[0]-sx)**2 + (n*p[1]-sy)**2)


def components(grid: Grid) -> list[Component]:
    """Four-connected single-color components, with no color semantics."""
    height, width = len(grid), len(grid[0])
    visited: set[tuple[int, int]] = set()
    result = []
    for y in range(height):
        for x in range(width):
            if (x, y) in visited:
                continue
            color = grid[y][x]
            stack = [(x, y)]
            visited.add((x, y))
            pixels = []
            while stack:
                px, py = stack.pop()
                pixels.append((px, py))
                for nx, ny in ((px-1, py), (px+1, py), (px, py-1), (px, py+1)):
                    if (0 <= nx < width and 0 <= ny < height
                            and (nx, ny) not in visited and grid[ny][nx] == color):
                        visited.add((nx, ny))
                        stack.append((nx, ny))
            result.append(Component(color, tuple(pixels)))
    return result


def candidate_actions(obs: Observation) -> list[Action]:
    actions = [Action(c) for c in obs.available if c not in (0, 6)]
    if 6 not in obs.available:
        return actions
    height, width = len(obs.grid), len(obs.grid[0])
    background = Counter(c for row in obs.grid for c in row).most_common(1)[0][0]
    objects = sorted(components(obs.grid), key=lambda c: (c.color == background, -len(c.pixels)))
    points = {c.center for c in objects[:64]}
    # A fixed lattice supplements object centers, including apparently empty cells.
    points.update((min(width-1, (2*x+1)*width//16),
                   min(height-1, (2*y+1)*height//16))
                  for x in range(8) for y in range(8))
    actions.extend(Action(6, x, y) for x, y in sorted(points))
    return actions


def action_family(obs: Observation, action: Action) -> str:
    if action.code != 6:
        return str(action.code)
    height, width = len(obs.grid), len(obs.grid[0])
    patch = tuple(obs.grid[y][x] if 0 <= x < width and 0 <= y < height else -1
                  for y in range(action.y-1, action.y+2)
                  for x in range(action.x-1, action.x+2))
    return "click:" + repr(patch)
