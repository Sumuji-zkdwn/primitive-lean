from .perception import Action


def to_sdk_action(action: Action):
    from arcengine import GameAction

    # arcengine's enum has a custom value property. GameAction(int) is invalid.
    return GameAction["RESET" if action.code == 0 else f"ACTION{action.code}"]
