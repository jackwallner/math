"""Graph builders for one-point unions (vertex amalgamations).

Vertex 0 is always the shared vertex c.
"""
from collections import deque


def cycle_windmill(m: int, n: int) -> tuple[int, list[tuple[int, int]]]:
    """n copies of C_m sharing vertex 0."""
    edges: list[tuple[int, int]] = []
    nv = 1
    for _ in range(n):
        cyc = [0] + list(range(nv, nv + m - 1))
        nv += m - 1
        edges += [(cyc[i], cyc[(i + 1) % m]) for i in range(m)]
    return nv, edges


def k2k_windmill(k: int, n: int) -> tuple[int, list[tuple[int, int]]]:
    """n copies of K_{2,k} glued at a vertex of degree k.

    Copy i has its second degree-k vertex d_i and k vertices x_{i,j},
    each adjacent to both 0 and d_i.
    """
    edges: list[tuple[int, int]] = []
    nv = 1
    for _ in range(n):
        d = nv
        xs = list(range(nv + 1, nv + 1 + k))
        nv += k + 1
        for x in xs:
            edges += [(0, x), (d, x)]
    return nv, edges


def two_colour(nv: int, edges: list[tuple[int, int]]) -> list[int]:
    """Bipartition by BFS from vertex 0 (class 0 contains vertex 0)."""
    adj: list[list[int]] = [[] for _ in range(nv)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = [-1] * nv
    side[0] = 0
    queue = deque([0])
    while queue:
        u = queue.popleft()
        for w in adj[u]:
            if side[w] < 0:
                side[w] = 1 - side[u]
                queue.append(w)
            elif side[w] == side[u]:
                raise ValueError("graph is not bipartite")
    if min(side) < 0:
        raise ValueError("graph is not connected")
    return side


def build(family: str, a: int, n: int) -> tuple[int, list[tuple[int, int]]]:
    if family == "C":
        return cycle_windmill(a, n)
    if family == "K2":
        return k2k_windmill(a, n)
    raise ValueError(family)
