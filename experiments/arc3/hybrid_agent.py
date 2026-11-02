"""Independent game-level policy switcher for ARC3 comparison runs.

The switch table records the seed-3 public comparison: retain the world model
for ls20/ft09 and the upstream Explore policy for vc33. Unknown games use the
world model as an explicit fallback; this is a comparison rule, not a claim of
generalization.
"""
from arc3.agent import WorldModelAgent
from explore_agent import ExploreAgent


POLICY_BY_GAME = {
    "ls20": "model",
    "ft09": "model",
    "vc33": "explore",
}


class HybridAgent:
    def __init__(self, game: str, seed: int = 0):
        self.game = game.lower().split("-")[0]
        self.selected_policy = POLICY_BY_GAME.get(self.game, "model")
        self.agent = (ExploreAgent(seed) if self.selected_policy == "explore"
                      else WorldModelAgent(seed))
        self.reason = "hybrid:" + self.selected_policy

    def observe(self, obs):
        self.agent.observe(obs)

    def after_reset(self, obs):
        self.agent.after_reset(obs)

    def act(self):
        action = self.agent.act()
        self.reason = "hybrid:" + self.selected_policy + ":" + self.agent.reason
        return action

    def metrics(self):
        return {
            "selected_policy": self.selected_policy,
            "policy_table": POLICY_BY_GAME,
            "unknown_game_fallback": "model",
            **self.agent.metrics(),
        }
