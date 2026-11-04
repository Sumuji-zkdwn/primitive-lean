import pytest

from arc3.perception import Action
from arc3.sdk import to_sdk_action


@pytest.mark.parametrize("code", range(8))
def test_action_converts_to_official_enum(code):
    pytest.importorskip("arcengine")
    action = Action(code, 12, 34) if code == 6 else Action(code)
    converted = to_sdk_action(action)
    assert converted.value == code
    assert converted.is_complex() == (code == 6)
