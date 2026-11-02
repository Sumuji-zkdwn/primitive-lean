"""Generated maze sanity check. These are NOT ARC-AGI-3 tasks or scores."""
from __future__ import annotations

import argparse
import json
import random

from .agent import WorldModelAgent
from .evaluate import RandomAgent
from .perception import Action, Observation


class Maze:
    def __init__(self, seed: int, size: int = 9) -> None:
        if size < 5 or size % 2 == 0:
            raise ValueError("Maze size must be odd and at least 5")
        rng = random.Random(seed)
        self.size = size
        self.open = {(1, 1)}
        stack = [(1, 1)]
        while stack:
            x, y = stack[-1]
            choices = [(x+dx, y+dy, dx, dy) for dx, dy in [(2,0),(-2,0),(0,2),(0,-2)]
                       if 0 < x+dx < size-1 and 0 < y+dy < size-1
                       and (x+dx, y+dy) not in self.open]
            if not choices:
                stack.pop()
                continue
            nx, ny, dx, dy = rng.choice(choices)
            self.open.update([(nx, ny), (x+dx//2, y+dy//2)])
            stack.append((nx, ny))
        moves = [(1,0),(-1,0),(0,1),(0,-1)]
        rng.shuffle(moves)
        self.moves = dict(zip(range(1,5), moves))
        self.palette = rng.sample(range(16), 4)
        self.position = (1, 1)
        self.goal = (size-2, size-2)

    def observation(self) -> Observation:
        wall, floor, player, goal = self.palette
        grid = tuple(tuple(player if (x,y) == self.position else goal if (x,y) == self.goal
                           else floor if (x,y) in self.open else wall
                           for x in range(self.size)) for y in range(self.size))
        won = self.position == self.goal
        return Observation(grid, (1,2,3,4), int(won), "WIN" if won else "NOT_FINISHED")

    def step(self, action: Action) -> Observation:
        dx, dy = self.moves[action.code]
        x, y = self.position
        if (x+dx, y+dy) in self.open:
            self.position = (x+dx, y+dy)
        return self.observation()


def benchmark(seeds: list[int], budget: int = 500) -> list[dict]:
    results = []
    for seed in seeds:
        for kind, agent in [("model", WorldModelAgent(seed)), ("random", RandomAgent(seed))]:
            env = Maze(seed)
            obs = env.observation()
            agent.observe(obs)
            steps = 0
            while steps < budget and not obs.terminal:
                obs = env.step(agent.act())
                agent.observe(obs)
                steps += 1
            results.append({"seed": seed, "agent": kind, "actions": steps,
                            "win": obs.status == "WIN", **agent.metrics()})
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=30)
    parser.add_argument("--budget", type=int, default=500)
    args = parser.parse_args()
    print(json.dumps(benchmark(list(range(args.seeds)), args.budget), indent=2))
