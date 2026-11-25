"""Python mirror of the kernel search in L_meta_12230's `Signed` section (BitVec 128 words).

A word holds a wire's values on 64 sample positions: bit k (k < 64) is the value on the TRUE row
of pair k, bit 64 + k the value on the FALSE row of pair k. `search n inputs` is true when some
sub-list of the inputs can be combined by at most n signed binary gates (and, or, and-not both
ways; complements free) into goal or its complement while every pair stays separated.
`search n rows = false` is what the Lean file proves with `decide +kernel`.
"""
from functools import lru_cache

M64 = (1 << 64) - 1
M128 = (1 << 128) - 1
GOAL = M64 << 64          # (-1 : BitVec 64) ++ (0 : BitVec 64)
NGOAL = M64               # ~~~goal


def ops(x, y):
    return [x & y, x | y, x & (~y & M128), y & (~x & M128)]


def sep(x):
    return ((x >> 64) ^ x) & M64


def cuts(ws):
    v = 0
    for w in ws:
        v |= sep(w)
    return v


def singles(l):
    if not l:
        return []
    a, rest = l[0], l[1:]
    return [(a, rest)] + [(b, [a] + bs) for (b, bs) in singles(rest)]


def pairs(l):
    if not l:
        return []
    a, rest = l[0], l[1:]
    return [(a, b, bs) for (b, bs) in singles(rest)] + [(b, c, [a] + bs) for (b, c, bs) in pairs(rest)]


@lru_cache(maxsize=None)
def optimized(k, extra, ws):
    ws = list(ws)
    if ws == [GOAL] or ws == [NGOAL]:
        return True
    if k == 0:
        return False
    for a, b, r in pairs(ws):
        if dispatch(extra, k - 1, a, b, r):
            return True
    return False


def nxt(k, extra, ws):
    return optimized(k, extra, tuple(sorted(ws)))


def dispatch(extra, k, a, b, r):
    base = cuts(r)
    for w in ops(a, b):
        v = sep(w) | base
        if v == M64 and nxt(k, extra, [w] + r):
            return True
        if extra != 0:
            if (v | sep(a)) == M64 and nxt(k, extra - 1, [w, a] + r):
                return True
            if (v | sep(b)) == M64 and nxt(k, extra - 1, [w, b] + r):
                return True
        if extra >= 2 and (v | sep(a) | sep(b)) == M64 and nxt(k, extra - 2, [w, a, b] + r):
            return True
    return False


def sublists(l):
    out = [[]]
    for x in l:
        out = out + [s + [x] for s in out]
    return out


def search(n, inputs):
    optimized.cache_clear()
    for ws in sublists(inputs):
        if len(ws) <= n + 1 and cuts(ws) == M64 and nxt(n, n + 1 - len(ws), ws):
            return True
    return False


def words(nvars, pair_list):
    """The input words for 64 (true row, false row) pairs (cycled to fill 64 positions)."""
    assert 1 <= len(pair_list) <= 64
    full = [pair_list[k % len(pair_list)] for k in range(64)]
    out = []
    for i in range(nvars):
        w = 0
        for k, (t, f) in enumerate(full):
            w |= ((t >> i) & 1) << k
            w |= ((f >> i) & 1) << (64 + k)
        out.append(w)
    return out
