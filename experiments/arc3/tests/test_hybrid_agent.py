import sys
import unittest
from pathlib import Path
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "runtime"))
sys.path.insert(0, str(HERE))

from hybrid_agent import HybridAgent


class StubAgent:
    def __init__(self, seed=0):
        self.seed = seed
        self.calls = []
        self.reason = "stub"

    def observe(self, obs):
        self.calls.append(("observe", obs))

    def after_reset(self, obs):
        self.calls.append(("after_reset", obs))

    def act(self):
        self.calls.append(("act",))
        return "action"

    def metrics(self):
        return {"stub_metric": 1}


class HybridAgentTests(unittest.TestCase):
    def test_routes_seed3_policy_table_and_unknown_fallback(self):
        with patch("hybrid_agent.WorldModelAgent", side_effect=StubAgent) as model, \
             patch("hybrid_agent.ExploreAgent", side_effect=StubAgent) as explore:
            cases = [("ls20-9607627b", "model"), ("ft09", "model"),
                     ("vc33-5430563c", "explore"), ("unlisted", "model")]
            for game, expected in cases:
                agent = HybridAgent(game, seed=17)
                self.assertEqual(agent.selected_policy, expected)
                constructor = model if expected == "model" else explore
                constructor.assert_called_with(17)

    def test_forwards_sdk_contract_and_metrics(self):
        with patch("hybrid_agent.WorldModelAgent", StubAgent):
            agent = HybridAgent("ls20", seed=2)
            obs = object()
            agent.observe(obs)
            agent.after_reset(obs)
            self.assertEqual(agent.act(), "action")
            self.assertEqual([item[0] for item in agent.agent.calls],
                             ["observe", "after_reset", "act"])
            self.assertEqual(agent.metrics()["stub_metric"], 1)
            self.assertEqual(agent.metrics()["selected_policy"], "model")


if __name__ == "__main__":
    unittest.main()
