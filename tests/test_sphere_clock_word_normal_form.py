"""Standalone exact finite regression for sphere-clock operation words.

Model: G=Z/12Z, H={0,3,6,9}; 24 raw sheet states, 20 quotient classes.
This is independent finite evidence, not a proof over R/Z.
"""
from itertools import product

N = 12
H = frozenset((0, 3, 6, 9))
RAW = list(product(range(N), (0, 1)))

def glued(p, q):
    return p[0] == q[0] and (p[1] == q[1] or p[0] in H)

def cls(p):
    return (p[0], 0 if p[0] in H else p[1])

def rotate(p, d):
    return ((p[0] + d) % N, p[1])

def flip(p):
    return (p[0], 1-p[1])

def run(p, word):
    trace = [cls(p)]
    for operation, amount in word:
        state = rotate(trace[-1], amount) if operation == "r" else flip(trace[-1])
        trace.append(cls(state))
    return trace

def normal(word):
    return (sum(amount for op, amount in word if op == "r") % N,
            sum(op == "f" for op, _ in word) % 2)

def normal_action(p, word):
    d, odd = normal(word)
    return cls(flip(rotate(p, d)) if odd else rotate(p, d))

CLASSES = sorted({cls(p) for p in RAW})
assert len(RAW) == 24 and len(CLASSES) == 20

# Verify equivalence and the exact admissibility boundary, on raw states.
for p in RAW:
    assert glued(p, p)
    for q in RAW:
        assert glued(p, q) == glued(q, p)
        for r in RAW:
            assert not (glued(p, q) and glued(q, r)) or glued(p, r)
for d in range(N):
    respects = all(not glued(p, q) or glued(rotate(p, d), rotate(q, d))
                   for p, q in product(RAW, repeat=2))
    assert respects == (d in H)

# 4 allowed rotations x 24 raw states = 96 commuting tests.
for d, p in product(H, RAW):
    assert glued(rotate(flip(p), d), flip(rotate(p, d)))
assert len(H) * len(RAW) == 96

# Every word up to length five over R_0,R_3,R_6,R_9,F:
# 1+5+25+125+625+3125=3906 words, each on 20 quotient states.
ALPHABET = [("r", d) for d in sorted(H)] + [("f", 0)]
words = 0
checks = 0
for length in range(6):
    for word in product(ALPHABET, repeat=length):
        words += 1
        assert normal(word)[0] in H
        for p in CLASSES:
            assert run(p, word)[-1] == normal_action(p, word)
            checks += 1
assert (words, checks) == (3906, 78120)

# Global action is faithful on the 20 classes in this finite case.
images_seen = set()
for d, odd in product(sorted(H), (0, 1)):
    images = tuple(cls(flip(rotate(p, d)) if odd else rotate(p, d))
                   for p in CLASSES)
    assert images not in images_seen
    images_seen.add(images)
assert len(images_seen) == 8

# Endpoints never reveal whether R_d or F came first.
# A sampled intermediate state does, except at glued points if d=0.
for d in sorted(H):
    first = [("r", d), ("f", 0)]
    second = [("f", 0), ("r", d)]
    assert all(run(p, first)[-1] == run(p, second)[-1] for p in CLASSES)
    distinct_histories = sum(run(p, first) != run(p, second) for p in CLASSES)
    assert distinct_histories == (16 if d == 0 else 20)

# At a glued point even the flip parity is invisible.
for p in CLASSES:
    assert (run(p, [("f", 0)])[-1] == p) == (p[0] in H)

print("PASS: raw=24 quotient=20 allowed_rotations=4 forbidden_rotations=8")
print("PASS: 96 commutations; 3906 words; 78120 normal-form checks")
print("PASS: 8 distinct global actions; histories distinguish 16/20 for d=0 and 20/20 otherwise")
