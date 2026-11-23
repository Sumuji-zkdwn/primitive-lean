# Hex Circuit — Lean 4 playable puzzle

This is a **playable game implemented in Lean 4**, not a Lean proof that merely
describes a game. The program reads terminal commands, simulates state changes,
and prints the resulting board. It needs no graphics engine or JavaScript.

From the repository root, with Lean 4.36.0-rc2 installed:

```sh
lean --run games/hex/HexGame.lean
```

Alternatively, from the pinned project toolchain:

```sh
cd lean
lake env lean --run ../games/hex/HexGame.lean
```

The board is an axial-coordinate hexagon of radius two (19 cells). Every cell
has an editable outgoing direction, initially 0 (east). Each tick moves the
token according to its current cell's direction. Going off the board loses.
Visiting all six cells adjacent to (0,0), then returning to the origin, wins.
A cell has only one outgoing direction, so you are building a deterministic
circuit; a move never automatically modifies a router.

Direction encoding: 0=E (+1,0), 1=NE (+1,-1), 2=NW (0,-1),
3=W (-1,0), 4=SW (-1,+1), 5=SE (0,+1).

Commands: `set q r dir`, `turn q r`, `step`, `run n`, `show`,
`reset`, `demo`, `help`, `quit`. The token is `@`, a visited
goal is `*`, and a digit is a router.

For example, here is one winning program:

```text
set 1 0 2
set 1 -1 3
set 0 -1 4
set -1 0 5
set -1 1 0
set 0 1 2
run 7
```

`demo` loads that solution directly.

## Verification and scope

```sh
lean --trust=0 games/hex/HexGame.lean
lean --run games/hex/HexGame.lean --self-test
```

The Lean source contains a general theorem that every successful checked
move stays inside the board, a theorem that off-board edits have no effect,
and kernel-evaluated examples for the 19-cell geometry, the seven-step win,
and the initial crash. The CI also executes the actual terminal program with
the input sequence above and checks the victory output.

This is **not** a proof of the physical behavior of a sandpile, the existence
of Laakso geometry, or the correctness of external graphics hardware.
Those are distinct experiments. Later work could replace the local router
rules with sandpile toppling, programmable agents, or multiple players, while
retaining executable transitions and local formal checks.
