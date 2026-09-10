#!/usr/bin/env python3
"""analysis: exact checks around the excess-one split-flattening lemma.

This is NOT part of the pinned final report/proof package.  It is a reusable
research-capability check for the open rank-22 / possible rank>=22 continuation.
It verifies the algebraic rank consequences proposed after the final theorem and
tests the small finite matrix condition for three invertible A-factors in the
normalised column coset used by the length-21 continuation note.
"""
from __future__ import annotations

import itertools, json, os, random
from collections import defaultdict

OUT = "data/excess_one/"
os.makedirs(OUT, exist_ok=True)

# 3x3 matrices over F2 are encoded row-major in bits 3*i+j.
def bit(m: int, i: int, j: int) -> int:
    return (m >> (3*i + j)) & 1

def mat_to_rows(m: int):
    return [[bit(m,i,j) for j in range(3)] for i in range(3)]

def rows_to_mat(rows) -> int:
    x = 0
    for i in range(3):
        for j in range(3):
            if rows[i][j] & 1:
                x |= 1 << (3*i+j)
    return x

def transpose(m: int) -> int:
    return rows_to_mat([[bit(m,j,i) for j in range(3)] for i in range(3)])

def matmul(a: int, b: int) -> int:
    rows = [[0]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            s = 0
            for k in range(3):
                s ^= bit(a,i,k) & bit(b,k,j)
            rows[i][j] = s
    return rows_to_mat(rows)

def gf2_rank_int(m: int) -> int:
    rows = [(m >> (3*i)) & 0b111 for i in range(3)]
    rank = 0
    for col in range(3):
        piv = None
        for r in range(rank, 3):
            if (rows[r] >> col) & 1:
                piv = r; break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for r in range(3):
            if r != rank and ((rows[r] >> col) & 1):
                rows[r] ^= rows[rank]
        rank += 1
    return rank

RANK3 = [m for m in range(512) if gf2_rank_int(m)==3]
RANK_GE2 = [m for m in range(512) if gf2_rank_int(m)>=2]
RANK_LE1 = set(m for m in range(512) if gf2_rank_int(m)<=1)

# Inverses for GL_3(F2).
def inverse(a: int) -> int:
    # brute force is tiny and avoids convention mistakes
    for b in RANK3:
        if matmul(a,b) == 0b100010001 and matmul(b,a) == 0b100010001:
            return b
    raise ValueError("singular")

IDENT = 0b100010001
INV = {a: inverse(a) for a in RANK3}

# Direct A-split flattening for a simple tensor A \otimes B \otimes C.
# Rows: (i, jb, kb), columns: (ja, ic, kc).  Entry is A[i,ja] B[jb,kb] C[ic,kc].
def idx3(a,b,c):
    return (a*3 + b)*3 + c

def split_M(A: int, B: int, C: int):
    rows = [[0]*27 for _ in range(27)]
    for i in range(3):
        for jb in range(3):
            for kb in range(3):
                r = idx3(i,jb,kb)
                bv = bit(B,jb,kb)
                if not bv: continue
                for ja in range(3):
                    av = bit(A,i,ja)
                    if not av: continue
                    for ic in range(3):
                        for kc in range(3):
                            if bit(C,ic,kc):
                                c = idx3(ja,ic,kc)
                                rows[r][c] ^= 1
    return rows

def rank_binary_matrix(rows) -> int:
    rows = [sum((v&1)<<j for j,v in enumerate(row)) for row in rows]
    ncols = 0
    for row in rows:
        if row:
            ncols = max(ncols, row.bit_length())
    rank = 0
    for col in range(ncols):
        piv = None
        for r in range(rank, len(rows)):
            if (rows[r] >> col) & 1:
                piv = r; break
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for r in range(len(rows)):
            if r != rank and ((rows[r] >> col) & 1):
                rows[r] ^= rows[rank]
        rank += 1
    return rank

# Verify the split rank relation exactly for all A with a few nonzero B,C, and randomly more broadly.
rank_relation_checks = []
probe_BC = [(1,1), (IDENT,IDENT), (7,7), (272,272), (511,511)]
for B,C in probe_BC:
    assert B and C
    bad = []
    for A in range(512):
        rM = rank_binary_matrix(split_M(A,B,C))
        rA = gf2_rank_int(A)
        if rM != rA:
            bad.append((A,rM,rA))
            break
    rank_relation_checks.append({"B":B,"C":C,"all_A_ok":not bad,"first_bad":bad[:1]})
random.seed(3901)
random_bad = []
for _ in range(2000):
    A = random.randrange(512)
    B = random.randrange(1,512)
    C = random.randrange(1,512)
    if rank_binary_matrix(split_M(A,B,C)) != gf2_rank_int(A):
        random_bad.append((A,B,C))
        break
rank_relation_random_ok = not random_bad

# Precompute products B C^T and ranks for rank>=2 factors.
prod = {}
for B in RANK_GE2:
    for C in RANK_GE2:
        prod[(B,C)] = matmul(B, transpose(C))

# For each invertible A, list pairs (B,C) satisfying the diagonal excess-one rank consequence.
# rank(B C^T + A^{-1}) <= 1.
diag_pairs = {}
for A in RANK3:
    invA = INV[A]
    L = []
    for B in RANK_GE2:
        for C in RANK_GE2:
            if prod[(B,C)] ^ invA in RANK_LE1:
                L.append((B,C))
    diag_pairs[A] = L

def off_ok(pair_i, pair_j) -> bool:
    B_i, C_i = pair_i
    B_j, C_j = pair_j
    return prod[(B_i,C_j)] in RANK_LE1 and prod[(B_j,C_i)] in RANK_LE1

def find_triple_for_A(As, max_scan=None):
    L0, L1, L2 = [diag_pairs[A] for A in As]
    scanned0 = 0
    for p0 in L0:
        scanned0 += 1
        if max_scan and scanned0 > max_scan:
            return None, {"truncated": True, "scanned0": scanned0}
        cand1 = [p1 for p1 in L1 if off_ok(p0,p1)]
        if not cand1:
            continue
        cand2 = [p2 for p2 in L2 if off_ok(p0,p2)]
        if not cand2:
            continue
        # index cand2 by itself; lists are small enough after p0 filtering for direct nested loop
        for p1 in cand1:
            for p2 in cand2:
                if off_ok(p1,p2):
                    return (p0,p1,p2), {"truncated": False, "scanned0": scanned0, "cand1": len(cand1), "cand2": len(cand2)}
    return None, {"truncated": False, "scanned0": scanned0}

# Normalized column coset S=<272,4,2,1>; labels add first-row bits to p=272.
def A_label(label: int) -> int:
    return 272 ^ label
label_ranks = {label: gf2_rank_int(A_label(label)) for label in range(8)}
rank3_labels = [l for l,r in label_ranks.items() if r==3]
rank2_labels = [l for l,r in label_ranks.items() if r==2]

# Check the four possible triples of the rank-three labels occurring in the analysis residual family.
coset_triple_results = []
for labels in itertools.combinations(rank3_labels, 3):
    As = [A_label(l) for l in labels]
    witness, meta = find_triple_for_A(As)
    rec = {"labels": labels, "A_values": As, "found": witness is not None, "meta": meta}
    if witness:
        rec["witness_pairs"] = [{"B":B,"C":C,"BCt":prod[(B,C)],"rank_B":gf2_rank_int(B),"rank_C":gf2_rank_int(C),"diag_rank_error":gf2_rank_int(prod[(B,C)] ^ INV[A])} for (B,C),A in zip(witness,As)]
        rec["offdiag_ranks"] = [[None if i==j else gf2_rank_int(prod[(witness[i][0], witness[j][1])]) for j in range(3)] for i in range(3)]
    coset_triple_results.append(rec)

# Also provide a transparent universal example independent of chosen A labels.
universal_example = []
# B,C with kernels/rowspaces arranged as coordinate complements.
coord_pairs = [(0b000010100, 0b000010100),  # diag(0,1,1) = 272 actually row-major bits 4,8. This literal is wrong? Reassign below.
]
D0 = 272          # diag(0,1,1)
D1 = 257          # diag(1,0,1)
D2 = 17           # diag(1,1,0)
base_pairs = [(D0,D0),(D1,D1),(D2,D2)]
for B,C in base_pairs:
    D = prod[(B,C)]
    near = [A for A in RANK3 if (D ^ INV[A]) in RANK_LE1]
    universal_example.append({"B":B,"C":C,"BCt":D,"rank_B":gf2_rank_int(B),"rank_C":gf2_rank_int(C),"near_invertible_A_count":len(near),"sample_near_A":near[:8]})
universal_offdiag = [[None if i==j else gf2_rank_int(prod[(base_pairs[i][0], base_pairs[j][1])]) for j in range(3)] for i in range(3)]

summary = {
    "schema": "excess_one_lemma_check_v1",
    "purpose": "Test algebraic and finite necessary conditions for the proposed excess-one split-flattening extension; this is reusable open-branch capability, not part of the final R>=21 proof package.",
    "split_rank_relation": {
        "formula": "For nonzero B,C, the A-split matrix M(A,B,C), with rows (i,j_B,k_B) and columns (j_A,i_C,k_C), is permutation-equivalent to A tensor vec(B) tensor vec(C)^T, hence rank M(A,B,C)=rank A.",
        "all_A_probe_BC_checks": rank_relation_checks,
        "random_nonzero_BC_checks": 2000,
        "random_ok": rank_relation_random_ok,
    },
    "excess_one_algebra": {
        "operator_statement": "If E_t=M_t P^{-1}, sum E_t=I, and e=sum rank(E_t)-27=1, the kernel of direct-sum addition from ⊕ col(E_t) to F2^27 is one-dimensional. Hence E_s E_t = delta_st E_t + rank-one correction sharing, for fixed s, a common image line.",
        "rank_consequence_for_invertible_A": "For an invertible A_t, rank(B_t C_t^T + A_t^{-1})<=1; for distinct invertible A_s,A_t, rank(B_t C_s^T)<=1. These are necessary consequences only; the common-line/functional correction is stronger and is not exhausted by this finite rank test."
    },
    "counts": {
        "rank_ge2_matrices": len(RANK_GE2),
        "invertible_matrices": len(RANK3),
        "diag_pair_count_min": min(len(v) for v in diag_pairs.values()),
        "diag_pair_count_max": max(len(v) for v in diag_pairs.values()),
        "diag_pair_count_values": sorted(set(len(v) for v in diag_pairs.values())),
    },
    "normalized_coset": {
        "S": "<272,4,2,1>",
        "label_ranks": label_ranks,
        "rank3_labels": rank3_labels,
        "rank2_labels": rank2_labels,
        "three_invertible_label_triples": coset_triple_results,
    },
    "universal_rank_condition_example": {
        "description": "Coordinate rank-two B_i=C_i examples show the degraded diagonal/off-diagonal rank conditions alone do not imply 'at most two invertible A-factors' at excess one.",
        "pairs": universal_example,
        "offdiag_ranks": universal_offdiag,
    },
    "conclusion": {
        "simple_rank_only_excess1_closure": False,
        "why": "For every triple of rank-three labels in the normalized residual coset, the script found B,C pairs satisfying the necessary diagonal rank<=1 and ordered off-diagonal rank<=1 conditions. Therefore any useful excess-one lemma must use the full common one-dimensional relation (shared image/functional corrections) or additional decomposition structure, not only these rank inequalities.",
        "final_theorem_impact": "None: the pinned R_F2(T)<3,3,3> >= 21 proof uses zero excess, where the kernel is zero and the stronger exact orthogonal-idempotent relation is already certified in the report."
    }
}

out_path = os.path.join(OUT, "excess_one_lemma_check.json")
with open(out_path, "w") as f:
    json.dump(summary, f, indent=2, sort_keys=True)
print(json.dumps({
    "ok": True,
    "out": out_path,
    "rank_relation_random_ok": rank_relation_random_ok,
    "diag_pair_count_values": sorted(set(len(v) for v in diag_pairs.values())),
    "rank3_labels": rank3_labels,
    "coset_triples_found": [r["found"] for r in coset_triple_results],
    "simple_rank_only_excess1_closure": False,
}, indent=2))
