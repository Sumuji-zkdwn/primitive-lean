"""ARC SDK adapter; protocol and task feedback enter only at this boundary."""
from arc3.perception import Action
from online import InteractionModel


class StructuralAgent:
    def __init__(self, seed=0):
        self.model = InteractionModel(seed)
        self.previous_action = None
        self.reason = "structural-experiment"

    @staticmethod
    def token(obs):
        # Keep exact raw values, equality only. No pixel arithmetic or segmentation.
        # Task progress/status are an external feedback channel, not state semantics.
        return obs.grid, obs.available

    def observe(self, obs):
        if self.previous_action is None:
            self.model.start(self.token(obs))
        else:
            feedback = float(obs.levels > self.current.levels) + float(obs.status == "WIN")
            feedback -= float(obs.status == "GAME_OVER")
            self.model.update(self.previous_action, self.token(obs), feedback)
        self.current = obs
        self.previous_action = None

    def after_reset(self, obs):
        self.previous_action = None
        self.observe(obs)

    def act(self):
        if self.previous_action is not None:
            raise RuntimeError("Observe the previous action result first")
        obs = self.current
        # The action-space geometry comes from the SDK contract. Draw all pixels
        # with equal probability; do not infer object centers or useful directions.
        actions = [Action(c) for c in obs.available if c not in (0, 6)]
        if 6 in obs.available:
            w, h = len(obs.grid[0]), len(obs.grid)
            # A bounded random candidate pool controls large action spaces.
            points = self.model.rng.sample(range(w*h), min(64, w*h))
            actions.extend(Action(6, p % w, p // w) for p in points)
        actions.extend(a for a in self.model.known_actions()
                       if a.code in obs.available)
        action = self.model.choose(actions)
        self.previous_action = action
        return action

    def metrics(self):
        return self.model.metrics()
