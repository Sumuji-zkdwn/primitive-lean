"""Decode curve words from exact x + 3y readings every three letters.

Start at (0, 0) heading east in the integer model of check_curve_word_chain.
Each argument is an absolute reading (omit the known initial zero).
Example: python tools/curve_word_decode.py 20 12 10
"""

import argparse
from itertools import product

from check_curve_word_chain import state


def codebooks():
    books = [{} for _ in range(4)]
    for letters in product("AB", repeat=3):
        word = "".join(letters)
        x, y, turn, _, _ = state(word)
        for heading, book in enumerate(books):
            delta = x + 3 * y
            if delta in book:
                raise ValueError(f"Ambiguous reading for heading {heading}: {delta}")
            book[delta] = (word, (heading + turn) % 4)
            x, y = -y, x
    return books


def decode(readings):
    books = codebooks()
    heading = previous = 0
    blocks = []
    for index, reading in enumerate(readings, start=1):
        delta = reading - previous
        if delta not in books[heading]:
            raise ValueError(f"Reading {index} ({reading}) is unreachable from {previous}")
        word, heading = books[heading][delta]
        blocks.append(word)
        previous = reading
    return "".join(blocks)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("readings", type=int, nargs="+")
    args = parser.parse_args()
    try:
        print(decode(args.readings))
    except ValueError as error:
        parser.error(str(error))
