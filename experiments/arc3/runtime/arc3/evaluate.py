from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.metadata
import json
import logging
import os
import random
import time
from pathlib import Path

from .agent import WorldModelAgent
from .perception import Action, Observation
from .sdk import to_sdk_action


class RandomAgent:
    def __init__(self, seed: int) -> None:
        self.rng = random.Random(seed)

    def observe(self, obs: Observation) -> None:
        self.current = obs

    after_reset = observe

    def act(self) -> Action:
        obs = self.current
        codes = [c for c in obs.available if c != 0]
        if not codes:
            raise RuntimeError("No legal gameplay action")
        code = self.rng.choice(codes)
        return (Action(code, self.rng.randrange(len(obs.grid[0])), self.rng.randrange(len(obs.grid)))
                if code == 6 else Action(code))

    def metrics(self) -> dict:
        return {}


def run(game: str, kind: str, seed: int, budget: int, max_resets: int,
        output: Path, environments: Path, raw_state: bool = False) -> dict:
    # Keep SDK credential logs out of console and recordings.
    os.environ.setdefault("MPLCONFIGDIR", str(output.resolve() / "mpl-cache"))
    os.environ.setdefault("XDG_CACHE_HOME", str(output.resolve() / "cache"))
    from arc_agi import Arcade, OperationMode

    logger = logging.getLogger("arc3.sdk")
    logger.setLevel(logging.ERROR)
    logger.propagate = False
    if not logger.handlers:
        logger.addHandler(logging.NullHandler())
    logging.getLogger("arc_agi.scorecard").setLevel(logging.ERROR)
    arc = Arcade(operation_mode=OperationMode.OFFLINE,
                 environments_dir=str(environments), logger=logger)
    started = time.perf_counter()
    if kind == "explore":
        from explore_agent import ExploreAgent
        agent = ExploreAgent(seed)
    elif kind == "structure":
        from arc_agent import StructuralAgent
        agent = StructuralAgent(seed)
    else:
        agent = WorldModelAgent(seed, abstract_counters=not raw_state) if kind == "model" else RandomAgent(seed)
    env = arc.make(game, seed=seed)
    if env is None:
        raise RuntimeError(f"Cannot load {game}; download public game files first")
    # Arcade.make performs an initial reset. It is counted in our budget.
    calls, resets, steps = 1, 0, 0
    obs = Observation.from_sdk(env.observation_space)
    agent.observe(obs)
    best_levels = obs.levels
    stem = f"{game}-{kind}-{seed}"
    error = None
    scorecard = None
    with gzip.open(output / f"{stem}.jsonl.gz", "wt", encoding="utf-8") as trace:
        def record(action: Action | None) -> None:
            trace.write(json.dumps({
                "call": calls, "action": action.token() if action else None,
                "levels": obs.levels, "status": obs.status, "grid": obs.grid,
                "available": obs.available,
                "animation_count": obs.animation_count,
                "reason": getattr(agent, "reason", "random"),
            }) + "\n")

        record(None)
        try:
            while calls < budget and obs.status != "WIN":
                if obs.status in {"GAME_OVER", "NOT_PLAYED"}:
                    if resets >= max_resets:
                        break
                    calls += 1
                    resets += 1
                    raw = env.reset()
                    obs = Observation.from_sdk(raw)
                    agent.after_reset(obs)
                    record(Action(0))
                else:
                    action = agent.act()
                    sdk_action = to_sdk_action(action)
                    calls += 1
                    steps += 1
                    raw = env.step(sdk_action, data=action.data)
                    obs = Observation.from_sdk(raw)
                    agent.observe(obs)
                    record(action)
                best_levels = max(best_levels, obs.levels)
        except Exception as exc:
            error = f"{type(exc).__name__}: {exc}"
        finally:
            scorecard = arc.close_scorecard()
    if kind == "model":
        agent.model.save(output / f"{stem}.model.json")
        (output / f"{stem}.representation.json").write_text(
            json.dumps(agent.metrics()["excluded_border_rows"]), encoding="utf-8")
    result = {
        "game": env.info.game_id, "agent": kind, "seed": seed,
        "budget": budget, "calls_including_initial_reset": calls,
        "gameplay_actions": steps, "resets_after_initial": resets,
        "best_levels_completed": best_levels, "final_levels_completed": obs.levels,
        "win": obs.status == "WIN", "final_status": obs.status,
        "local_sdk_score": scorecard.score if scorecard is not None else None,
        "seconds": round(time.perf_counter()-started, 3),
        "error": error, **agent.metrics(),
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description="Offline public ARC-AGI-3 evaluation")
    parser.add_argument("--games", nargs="+", default=["ls20", "ft09", "vc33"])
    parser.add_argument("--agents", nargs="+", choices=["model", "random", "structure", "explore"], default=["model", "random"])
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 2])
    parser.add_argument("--budget", type=int, default=500)
    parser.add_argument("--max-resets", type=int, default=8)
    parser.add_argument("--raw-state", action="store_true", help="Disable counter abstraction for ablation")
    parser.add_argument("--environments", type=Path, default=Path("environment_files"))
    parser.add_argument("--output", type=Path, default=Path("results/public"))
    args = parser.parse_args()
    if args.budget < 1 or args.max_resets < 0:
        parser.error("budget must be positive and max-resets nonnegative")
    args.output.mkdir(parents=True, exist_ok=False)
    metadata = {
        "purpose": "Public development evaluation; not an official or hidden-test score",
        "packages": {p: importlib.metadata.version(p) for p in ["arc-agi", "arcengine", "numpy"]},
        "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(Path(__file__).parent.glob("*.py"))},
        "arguments": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
    }
    if "structure" in args.agents:
        import arc_agent
        import online
        metadata["structural_source_sha256"] = {
            Path(m.__file__).name: hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (arc_agent, online)}
    if "explore" in args.agents:
        import explore_agent
        import online
        from vendor.explore import compat, heuristic_agent, graph_explorer
        metadata["explore_source_sha256"] = {
            str(Path(m.__file__).relative_to(Path(explore_agent.__file__).parent)):
                hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (explore_agent, online, compat, heuristic_agent, graph_explorer)}
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2), encoding="utf-8")
    results = []
    for game in args.games:
        for seed in args.seeds:
            for kind in args.agents:
                result = run(game, kind, seed, args.budget, args.max_resets,
                             args.output, args.environments, args.raw_state)
                results.append(result)
                print(json.dumps(result), flush=True)
                (args.output / "summary.json").write_text(json.dumps(results, indent=2), encoding="utf-8")
    if any(r["error"] for r in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
