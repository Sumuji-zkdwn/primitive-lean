"""Local protocol only: upstream HTTP runner and tracing are not imported."""
from dataclasses import dataclass
from enum import Enum


class Agent:
    def __init__(self, seed=0):
        self.seed = seed
        self.game_id = 'offline'
        self.action_counter = 0

    @property
    def name(self):
        return 'explore-adapter'


def trace_agent_session(function):
    return function


class GameState(Enum):
    NOT_PLAYED = 'NOT_PLAYED'
    NOT_FINISHED = 'NOT_FINISHED'
    WIN = 'WIN'
    GAME_OVER = 'GAME_OVER'


class GameAction(Enum):
    RESET = 0
    ACTION1 = 1
    ACTION2 = 2
    ACTION3 = 3
    ACTION4 = 4
    ACTION5 = 5
    ACTION6 = 6
    ACTION7 = 7

    def set_data(self, data):
        self.data = data

    def is_simple(self):
        return self.value != 6

    def is_complex(self):
        return self.value == 6


@dataclass
class FrameData:
    frame: list
    available_actions: list
    state: GameState
    score: int
