"""Resolve the API-visible demo catalog without opening/playing any game."""
import argparse
from datetime import datetime, timezone
import json
import logging
import os
from pathlib import Path
import re


def select_games(game_ids, selection="all"):
    available = sorted(game_ids)
    if not available or len(available) != len(set(available)):
        raise ValueError("Demo catalog is empty or contains duplicate IDs")
    if any(not re.fullmatch(r"[a-z0-9_]+(?:-[a-z0-9_]+)?", item) for item in available):
        raise ValueError("Unexpected catalog game ID")
    if selection.strip() == "all":
        return available
    requested = selection.split()
    if not requested or len(requested) != len(set(requested)):
        raise ValueError("Explicit game selection is empty or duplicated")
    selected = []
    for item in requested:
        matches = [game for game in available if game == item or ("-" not in item and game.split("-", 1)[0] == item)]
        if len(matches) != 1:
            raise ValueError(f"Explicit game must match one catalog entry: {item}")
        selected.append(matches[0])
    if len(selected) != len(set(selected)):
        raise ValueError("Several requested IDs resolve to the same game")
    return selected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selection", default="all")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    from arc_agi import Arcade, OperationMode
    logger = logging.getLogger("arc3.demo-catalog")
    logger.handlers = [logging.NullHandler()]
    logger.propagate = False
    logger.setLevel(logging.CRITICAL)
    arc = Arcade(operation_mode=OperationMode.NORMAL, logger=logger)
    if arc.operation_mode != OperationMode.NORMAL:
        raise ValueError("Demo catalog discovery requires NORMAL mode")
    available = sorted(env.game_id for env in arc.get_environments())
    selected = select_games(available, args.selection)
    report = {"observed_utc": datetime.now(timezone.utc).isoformat(),
              "dataset_role": "Public Demo / development diagnostics",
              "source": "ARC Toolkit Arcade.get_environments in NORMAL mode",
              "catalog_game_count": len(available), "catalog_game_ids": available,
              "requested_selection": args.selection, "selected_game_count": len(selected),
              "selected_game_ids": selected, "game_actions": 0,
              "generalization_measurement": False,
              "scope": "API-visible demo catalog; no claim about hidden or competition coverage"}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if os.environ.get("GITHUB_ENV"):
        with open(os.environ["GITHUB_ENV"], "a", encoding="utf-8") as stream:
            stream.write("ARC3_GAMES=" + " ".join(selected) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
