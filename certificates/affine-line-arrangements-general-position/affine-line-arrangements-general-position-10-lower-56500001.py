#!/usr/bin/env python3
"""Deterministic witness candidates for arrangements of ten affine lines.

Standard-library Python 3 only. One row contains 30 integers a b c,
representing ten lines a*x+b*y=c. Repeated combinatorial types may occur:
a trusted verifier must check general position and count distinct types.

The candidate sequence uses an elementary fixed-seed random sampler,
independent of the larger unpublished research construction.
"""
import random
import sys

SEED = 20261120 ^ 0x56a56a5637f1
DRAWS = 136_500_000

# Zero-based draws that fail the general-position test. Independently
# derived by exhaustive determinant checks; the trusted checker must
# independently validate every emitted arrangement.
SKIP = frozenset((
    1965436, 4365613, 36269331, 45623105,
    49578173, 70023443, 94136785, 103504311,
))

def main():
    rng = random.Random(SEED)
    rand64 = rng.getrandbits
    write = sys.stdout.buffer.write
    pending = bytearray()
    for row in range(DRAWS):
        slopes = [0]
        offsets = [0]
        for _ in range(9):
            slopes.append(slopes[-1] + 1 + rand64(64) % 31)
            offsets.append(rand64(64) % 60_000_001 - 30_000_000)
        if row in SKIP:
            continue
        pending.extend((' '.join(f'{-s} 1 {t}' for s,t in zip(slopes, offsets))+'\n').encode())
        if len(pending) >= 1 << 20:
            write(pending)
            pending.clear()
    if pending:
        write(pending)

if __name__ == '__main__':
    main()
