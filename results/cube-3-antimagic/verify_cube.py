"""Check the 3-antimagic labeling of type (1,1,1) of the cube C4 x P2 (no dependencies)."""

# Vertices are the bit vectors 0..7; edges join u and u xor 2^b; each face fixes one bit.
VERTEX = [18, 16, 14, 2, 26, 21, 20, 24]
EDGE_LABELS = [8, 22, 19, 23, 9, 13, 6, 25, 3, 5, 4, 7]  # edges (u, u ^ 2^b), u < u ^ 2^b, by u then b
FACE = {(0, 0): 1, (0, 1): 10, (1, 0): 17, (1, 1): 11, (2, 0): 12, (2, 1): 15}  # (bit, value) -> label


def main() -> None:
    edges = [(u, u ^ (1 << b)) for u in range(8) for b in range(3) if u < u ^ (1 << b)]
    edge = dict(zip(edges, EDGE_LABELS))
    labels = VERTEX + EDGE_LABELS + list(FACE.values())
    assert sorted(labels) == list(range(1, 27)), "labels are not a bijection onto 1..26"
    weights = []
    for (bit, val), face_label in FACE.items():
        vs = [u for u in range(8) if (u >> bit) & 1 == val]
        es = [lab for (u, w), lab in edge.items() if u in vs and w in vs]
        assert len(vs) == 4 and len(es) == 4
        weights.append(face_label + sum(VERTEX[u] for u in vs) + sum(es))
    w = sorted(weights)
    assert all(b - a == 3 for a, b in zip(w, w[1:])), w
    print("face weights:", w, "-> arithmetic progression with difference 3. OK")


if __name__ == "__main__":
    main()
