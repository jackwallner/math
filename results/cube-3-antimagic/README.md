# The cube has a 3-antimagic labeling of type (1,1,1)

**Status:** settles the case d = 3, n = 4 of the d-antimagic labeling problem for prisms C_n x P_2, listed as open in Gallian's *Dynamic Survey of Graph Labeling* (2026 edition). Bača, Miller and Ryan settled d = 3 for n ≠ 4.

**Definition.** A labeling of type (1,1,1) assigns 1, 2, ..., |V| + |E| + |F| bijectively to the vertices, edges and faces of a plane graph. The weight of a face is its own label plus the labels of its vertices and edges. The labeling is d-antimagic if, for each s, the weights of the s-sided faces form an arithmetic progression with difference d. All six faces of the cube are 4-sided (the outer face included), so one 6-term progression is required.

**The labeling.** Number the vertices 0..7 as bit vectors; edges join u and u xor 2^b; each face fixes one bit.

| Element | Labels |
| --- | --- |
| Vertices 0..7 | 18, 16, 14, 2, 26, 21, 20, 24 |
| Edges (u, u xor 2^b), u < u xor 2^b, ordered by u then b | 8, 22, 19, 23, 9, 13, 6, 25, 3, 5, 4, 7 |
| Faces bit0=0, bit0=1, bit1=0, bit1=1, bit2=0, bit2=1 | 1, 10, 17, 11, 12, 15 |

Face weights: 131, 134, 137, 122, 128, 125, that is 122, 125, ..., 137 with difference 3.

**Check it:** `python3 verify_cube.py` (no dependencies). Found with a constraint solver and re-checked by two independent scripts.
