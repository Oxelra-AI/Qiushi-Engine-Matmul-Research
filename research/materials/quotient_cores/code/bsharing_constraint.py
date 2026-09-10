#!/usr/bin/env python3
"""
analysis: Verify the B/C-sharing constraint from split-flattening column/row structure.

Key claim (review, analysis):
  col(M_t) = col(A_t^mat) ⊗ ⟨vec(B_t)⟩   as a subspace of F_2^3 ⊗ F_2^9 = F_2^27
  row(M_t) = row(A_t^mat) ⊗ ⟨vec(C_t)⟩   as a subspace of F_2^3 ⊗ F_2^9 = F_2^27

Consequence: if several summands share the same B_t = b, their column spaces
all lie in F^3 ⊗ ⟨vec(b)⟩, a 3-dimensional subspace.  Since the global kernel
of the addition map ⊕_t col(M_t) → F_2^27 has dimension e = Σ rank(A_t) − 27,
every subfamily's defect embeds in that kernel, giving:

  Σ_{t: B_t = b} rank(A_t)  ≤  3 + e_A      (column constraint)
  Σ_{t: C_t = c} rank(A_t)  ≤  3 + e_A      (row constraint)

Under cyclic symmetry (A,B,C) → (B,C^T,A^T) this transfers to all slots.

Verification plan:
  1. Build M_t = Φ_A(A_t ⊗ B_t ⊗ C_t) and check col(M_t) = col(A_t) ⊗ ⟨vec(B_t)⟩
  2. Check rank(M_t) = rank(A_t)
  3. Verify Σ M_t = P (the 27×27 permutation matrix)
  4. Group rank-23 terms by B value; check A-rank sum ≤ 3 + e_A
  5. Group rank-23 terms by C value; check A-rank sum ≤ 3 + e_A
  6. Derive and check the B-split and C-split versions
"""

import json, os, numpy as np
from pathlib import Path
from collections import defaultdict

ROOT = Path(os.environ.get("QIUSHI_USER_ROOT", "."))
WS   = ROOT / "research" / "research_record" / "workspace"
OUT  = WS / "data" / "bsharing"
OUT.mkdir(parents=True, exist_ok=True)

F2 = np.uint8  # work in F_2

def int_to_mat(v):
    """Integer v → 3×3 matrix over F_2, entry (i,j) = bit at position 3i+j."""
    m = np.zeros((3,3), dtype=F2)
    for i in range(3):
        for j in range(3):
            m[i,j] = (v >> (3*i+j)) & 1
    return m

def mat_to_int(m):
    v = 0
    for i in range(3):
        for j in range(3):
            if m[i,j] & 1:
                v |= 1 << (3*i+j)
    return v

def f2_rank(m):
    """Rank of a matrix over F_2 via Gaussian elimination."""
    m = m.astype(np.int32).copy()
    rows, cols = m.shape
    r = 0
    for c in range(cols):
        piv = None
        for rr in range(r, rows):
            if m[rr, c] & 1:
                piv = rr
                break
        if piv is None:
            continue
        m[[r, piv]] = m[[piv, r]]
        for rr in range(rows):
            if rr != r and (m[rr, c] & 1):
                m[rr] ^= m[r]
        r += 1
    return r

def f2_col_space(m):
    """Return a set of tuples representing the column space of m over F_2."""
    m = m.astype(np.int32)
    rows, cols = m.shape
    # columns of m generate the column space
    gens = [m[:, c] % 2 for c in range(cols) if np.any(m[:, c] % 2)]
    # enumerate span
    span = {tuple(np.zeros(rows, dtype=int))}
    for g in gens:
        new = set()
        for v in span:
            w = tuple((np.array(v) ^ g) % 2)
            new.add(w)
        span |= new
    return span

def build_split_flattened(A, B, C):
    """Build the 27×27 A-split flattened matrix M(A,B,C).
    Rows: (i, b) with i∈{0,1,2}, b∈{0,...,8}  → row index = 9*i + b
    Cols: (j, c) with j∈{0,1,2}, c∈{0,...,8}  → col index = 9*j + c
    M[(i,b),(j,c)] = A[i,j] * B_vec[b] * C_vec[c]
    """
    A_mat = int_to_mat(A)
    B_vec = np.zeros(9, dtype=F2)
    C_vec = np.zeros(9, dtype=F2)
    for idx in range(9):
        B_vec[idx] = (B >> idx) & 1
        C_vec[idx] = (C >> idx) & 1
    M = np.zeros((27, 27), dtype=F2)
    for i in range(3):
        for j in range(3):
            for b in range(9):
                for c in range(9):
                    M[9*i+b, 9*j+c] = (A_mat[i,j] * B_vec[b] * C_vec[c]) & 1
    return M

def build_tensor_P():
    """Build the 27×27 A-split flattening of the tensor T[3i+j,3j+k,3i+k]=1."""
    P = np.zeros((27, 27), dtype=F2)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                a = 3*i + j  # A-index
                b = 3*j + k  # B-index
                c = 3*i + k  # C-index
                row = 9*(a//3) + b  # (i, b) where a=3i+j, so row of A = i
                # Wait: the A-split splits a=3i+j into (i,j), so
                # row index = 9*i + b, col index = 9*j + c
                P[9*i + b, 9*j + c] = 1
    return P

def verify_column_space_structure(A_int, B_int, C_int, M):
    """Verify col(M) = col(A_mat) ⊗ ⟨vec(B)⟩ in F_2^27."""
    A_mat = int_to_mat(A_int)
    B_vec = np.zeros(9, dtype=np.int32)
    for idx in range(9):
        B_vec[idx] = (B_int >> idx) & 1
    
    # Build the predicted column space: col(A_mat) ⊗ ⟨vec(B)⟩
    # A column of A_mat is a 3-vector; tensored with vec(B) gives a 27-vector
    # The tensor product v ⊗ w has entry (9*i + b) = v[i] * w[b]
    rk_A = f2_rank(A_mat.astype(np.int32))
    
    # Get basis for col(A_mat)
    a_cols_used = []
    temp = A_mat.astype(np.int32).copy()
    # Just get column space generators
    a_col_gens = [A_mat[:, j].astype(np.int32) % 2 for j in range(3)]
    
    # Build tensor products as generators
    predicted_gens = []
    for j in range(3):
        a_col = A_mat[:, j].astype(np.int32) % 2
        if not np.any(a_col):
            continue
        gen = np.zeros(27, dtype=np.int32)
        for i in range(3):
            for b in range(9):
                gen[9*i + b] = (a_col[i] * B_vec[b]) % 2
        predicted_gens.append(gen)
    
    # Get actual column space generators from M
    M_int = M.astype(np.int32) % 2
    actual_gens = [M_int[:, c] for c in range(27) if np.any(M_int[:, c])]
    
    # Compute both spans and compare
    def span_of(gens, dim=27):
        s = {tuple(np.zeros(dim, dtype=int))}
        for g in gens:
            new = set()
            for v in s:
                w = tuple((np.array(v) ^ g) % 2)
                new.add(w)
            s |= new
        return s
    
    pred_span = span_of(predicted_gens)
    actual_span = span_of(actual_gens)
    
    return pred_span == actual_span, len(pred_span) - 1, len(actual_span) - 1

def transpose_int(v):
    """Transpose a 3×3 F_2 matrix given as integer."""
    m = int_to_mat(v)
    return mat_to_int(m.T)

# ================================================================
# Load rank-23 scheme
# ================================================================
ctrl_path = WS / "data" / "pivot_fixed" / "pivot17_rank23_transformed_control.json"
with open(ctrl_path) as f:
    ctrl = json.load(f)
terms = ctrl["terms"]  # [[A, B, C], ...]
n_terms = len(terms)

print(f"Loaded rank-23 scheme with {n_terms} terms")

# ================================================================
# 1. Build tensor P and verify it's a permutation matrix
# ================================================================
P = build_tensor_P()
assert np.sum(P) == 27, "P should have exactly 27 ones"
assert all(np.sum(P[r]) == 1 for r in range(27)), "Each P row should have exactly one 1"
assert all(np.sum(P[:, c]) == 1 for c in range(27)), "Each P column should have exactly one 1"
print("✓ P is a 27×27 permutation matrix")

# ================================================================
# 2. Build all M_t, check rank(M_t) = rank(A_t), verify Σ M_t = P
# ================================================================
Ms = []
rank_A = []
rank_B = []
rank_C = []
sum_M = np.zeros((27, 27), dtype=F2)

for t, (A, B, C) in enumerate(terms):
    M_t = build_split_flattened(A, B, C)
    Ms.append(M_t)
    rA = f2_rank(int_to_mat(A).astype(np.int32))
    rB = f2_rank(int_to_mat(B).astype(np.int32))
    rC = f2_rank(int_to_mat(C).astype(np.int32))
    rM = f2_rank(M_t.astype(np.int32))
    rank_A.append(rA)
    rank_B.append(rB)
    rank_C.append(rC)
    assert rM == rA, f"Term {t}: rank(M_t)={rM} != rank(A_t)={rA}"
    sum_M = (sum_M + M_t) % 2

assert np.array_equal(sum_M % 2, P), "Σ M_t should equal P"
print("✓ rank(M_t) = rank(A_t) for all t, and Σ M_t = P")

e_A = sum(rank_A) - 27
e_B = sum(rank_B) - 27
e_C = sum(rank_C) - 27
print(f"  A-excess e_A = {e_A},  B-excess e_B = {e_B},  C-excess e_C = {e_C}")

# ================================================================
# 3. Verify column-space structure col(M_t) = col(A_t) ⊗ ⟨vec(B_t)⟩
# ================================================================
col_checks = 0
for t, (A, B, C) in enumerate(terms):
    ok, pred_dim, actual_dim = verify_column_space_structure(A, B, C, Ms[t])
    assert ok, f"Term {t}: column space mismatch (pred dim {pred_dim}, actual dim {actual_dim})"
    col_checks += 1
print(f"✓ col(M_t) = col(A_t) ⊗ ⟨vec(B_t)⟩ verified for all {col_checks} terms")

# ================================================================
# 4. B-sharing constraint: Σ_{t: B_t=b} rank(A_t) ≤ 3 + e_A
# ================================================================
b_groups = defaultdict(list)
for t, (A, B, C) in enumerate(terms):
    b_groups[B].append(t)

b_sharing_results = []
b_max_sum = 0
for b_val, indices in sorted(b_groups.items()):
    a_rank_sum = sum(rank_A[t] for t in indices)
    b_max_sum = max(b_max_sum, a_rank_sum)
    ok = a_rank_sum <= 3 + e_A
    b_sharing_results.append({
        "B_value": b_val,
        "term_indices": indices,
        "A_ranks": [rank_A[t] for t in indices],
        "A_rank_sum": a_rank_sum,
        "bound": 3 + e_A,
        "ok": ok
    })
    if len(indices) > 1:
        print(f"  B={b_val}: terms {indices}, A-ranks {[rank_A[t] for t in indices]}, sum={a_rank_sum}, bound={3+e_A}, {'✓' if ok else '✗'}")

b_all_ok = all(r["ok"] for r in b_sharing_results)
print(f"{'✓' if b_all_ok else '✗'} B-sharing constraint (A-col): max A-rank sum = {b_max_sum}, bound = {3+e_A}")

# ================================================================
# 5. C-sharing constraint: Σ_{t: C_t=c} rank(A_t) ≤ 3 + e_A
# ================================================================
c_groups = defaultdict(list)
for t, (A, B, C) in enumerate(terms):
    c_groups[C].append(t)

c_sharing_results = []
c_max_sum = 0
for c_val, indices in sorted(c_groups.items()):
    a_rank_sum = sum(rank_A[t] for t in indices)
    c_max_sum = max(c_max_sum, a_rank_sum)
    ok = a_rank_sum <= 3 + e_A
    c_sharing_results.append({
        "C_value": c_val,
        "term_indices": indices,
        "A_ranks": [rank_A[t] for t in indices],
        "A_rank_sum": a_rank_sum,
        "bound": 3 + e_A,
        "ok": ok
    })
    if len(indices) > 1:
        print(f"  C={c_val}: terms {indices}, A-ranks {[rank_A[t] for t in indices]}, sum={a_rank_sum}, bound={3+e_A}, {'✓' if ok else '✗'}")

c_all_ok = all(r["ok"] for r in c_sharing_results)
print(f"{'✓' if c_all_ok else '✗'} C-sharing constraint (A-row): max A-rank sum = {c_max_sum}, bound = {3+e_A}")

# ================================================================
# 6. B-split versions via cyclic symmetry (A,B,C) → (B,C^T,A^T)
#    B-col: Σ_{t: C_t=c} rank(B_t) ≤ 3 + e_B
#    B-row: Σ_{t: A_t=a} rank(B_t) ≤ 3 + e_B
# ================================================================
# B-col: group by C value, sum B-ranks
bc_col_max = 0
for c_val, indices in sorted(c_groups.items()):
    b_rank_sum = sum(rank_B[t] for t in indices)
    bc_col_max = max(bc_col_max, b_rank_sum)
    if b_rank_sum > 3 + e_B:
        print(f"  ✗ B-col: C={c_val}, B-rank sum={b_rank_sum} > {3+e_B}")

# B-row: group by A value, sum B-ranks
a_groups = defaultdict(list)
for t, (A, B, C) in enumerate(terms):
    a_groups[A].append(t)
br_max = 0
for a_val, indices in sorted(a_groups.items()):
    b_rank_sum = sum(rank_B[t] for t in indices)
    br_max = max(br_max, b_rank_sum)
    if b_rank_sum > 3 + e_B:
        print(f"  ✗ B-row: A={a_val}, B-rank sum={b_rank_sum} > {3+e_B}")

# C-col: group by A value, sum C-ranks
cc_col_max = 0
for a_val, indices in sorted(a_groups.items()):
    c_rank_sum = sum(rank_C[t] for t in indices)
    cc_col_max = max(cc_col_max, c_rank_sum)
    if c_rank_sum > 3 + e_C:
        print(f"  ✗ C-col: A={a_val}, C-rank sum={c_rank_sum} > {3+e_C}")

# C-row: group by B value, sum C-ranks
cr_max = 0
for b_val, indices in sorted(b_groups.items()):
    c_rank_sum = sum(rank_C[t] for t in indices)
    cr_max = max(cr_max, c_rank_sum)
    if c_rank_sum > 3 + e_C:
        print(f"  ✗ C-row: B={b_val}, C-rank sum={c_rank_sum} > {3+e_C}")

print(f"B-split column (group by C): max B-rank sum = {bc_col_max}, bound = {3+e_B}")
print(f"B-split row (group by A): max B-rank sum = {br_max}, bound = {3+e_B}")
print(f"C-split column (group by A): max C-rank sum = {cc_col_max}, bound = {3+e_C}")
print(f"C-split row (group by B): max C-rank sum = {cr_max}, bound = {3+e_C}")

all_six_ok = (
    b_all_ok and c_all_ok
    and bc_col_max <= 3 + e_B
    and br_max <= 3 + e_B
    and cc_col_max <= 3 + e_C
    and cr_max <= 3 + e_C
)

# ================================================================
# 7. Zero-excess analysis for length-22 profiles
# ================================================================
print("\n=== Zero-excess implications for length-22 ===")
# At e_A=0: Σ_{t: B_t=b} rank(A_t) ≤ 3
# At e_A=0: Σ_{t: C_t=c} rank(A_t) ≤ 3
# Profile (18,3,1): 18 rank-one, 3 rank-two, 1 rank-three A-factors
# The rank-3 factor must have a unique B (since rank 3 = cap)
# Each rank-2 can share B with at most one rank-1 factor
# So at least 1 + 3 = 4 distinct B values are needed just for the high-rank terms

zero_excess_analysis = {
    "e_A=0_B_sharing_cap": 3,
    "profile_18_3_1": {
        "rank3_needs_unique_B": True,
        "rank2_can_share_B_with_at_most_one_rank1": True,
        "minimum_distinct_B_for_high_rank": 4,
        "note": "rank-3 uses cap 3 alone; each rank-2 uses cap 2, can share with one rank-1"
    },
    "profile_17_5_0": {
        "rank2_pairwise_sharing": "Two rank-2 cannot share B (sum=4>3)",
        "rank2_can_share_B_with_rank1": "Yes, sum=3=cap",
        "minimum_distinct_B_for_high_rank": 5,
        "note": "All 5 rank-2 need distinct B values; each can share with one rank-1"
    }
}

# ================================================================
# 8. Additional check: at e=0 the three invertible A-factors need distinct B values
# ================================================================
# From the report: at e=0 in length 20, the three rank-3 A-factors give
# col(M_t) = F^3 ⊗ ⟨vec(B_t)⟩ which is a full 3-dimensional slice.
# These three slices must be in direct sum (at e=0), so the three vec(B_t)
# must be distinct (in fact linearly independent is not needed, just that
# each slice F^3 ⊗ ⟨vec(B_t)⟩ is distinct).
# Actually: at e=0 the column spaces form a direct sum. If B_s = B_t for
# two rank-3 factors, then col(M_s) and col(M_t) both equal F^3 ⊗ ⟨vec(B)⟩,
# which has dimension 3. Their sum is also dimension 3, but rank(M_s)+rank(M_t)=6.
# This contradicts direct sum. So rank-3 factors MUST have distinct B values.

# ================================================================
# Compile results
# ================================================================
result = {
    "ok": all_six_ok,
    "rank23_scheme_source": str(ctrl_path),
    "n_terms": n_terms,
    "excess": {"e_A": e_A, "e_B": e_B, "e_C": e_C},
    "column_space_verified": True,
    "rank_relation_verified": True,
    "sum_Mt_equals_P": True,
    "six_constraints": {
        "A_col_by_B": {"max_sum": b_max_sum, "bound": 3+e_A, "ok": b_all_ok},
        "A_row_by_C": {"max_sum": c_max_sum, "bound": 3+e_A, "ok": c_all_ok},
        "B_col_by_C": {"max_sum": bc_col_max, "bound": 3+e_B, "ok": bc_col_max <= 3+e_B},
        "B_row_by_A": {"max_sum": br_max, "bound": 3+e_B, "ok": br_max <= 3+e_B},
        "C_col_by_A": {"max_sum": cc_col_max, "bound": 3+e_C, "ok": cc_col_max <= 3+e_C},
        "C_row_by_B": {"max_sum": cr_max, "bound": 3+e_C, "ok": cr_max <= 3+e_C},
    },
    "b_sharing_details": [r for r in b_sharing_results if len(r["term_indices"]) > 1],
    "c_sharing_details": [r for r in c_sharing_results if len(r["term_indices"]) > 1],
    "zero_excess_analysis": zero_excess_analysis,
    "theorem_statement": (
        "For T=<3,3,3> over F_2, let T = Σ_{t=1}^n A_t⊗B_t⊗C_t be an exact decomposition. "
        "Set e_A = Σ rank(A_t) - 27.  Then for every 3×3 matrix b over F_2, "
        "Σ_{t: B_t=b} rank(A_t) ≤ 3 + e_A, and dually for C.  "
        "Under the cyclic symmetry (A,B,C)→(B,C^T,A^T), analogous bounds hold for B-split "
        "(grouping by C or A) and C-split (grouping by A or B), each with the corresponding slot excess."
    ),
    "proof_sketch": (
        "The A-split flattened summand M_t = A_t ⊗ (vec(B_t)·vec(C_t)^T) has "
        "col(M_t) = col(A_t) ⊗ ⟨vec(B_t)⟩ ⊂ F_2^3 ⊗ ⟨vec(B_t)⟩.  "
        "Since Σ M_t = P is invertible of rank 27, the addition map from ⊕_t col(M_t) → F_2^27 "
        "is surjective with kernel of dimension e_A.  For any subfamily sharing B_t = b, "
        "their column spaces all lie in the 3-dimensional slice F_2^3 ⊗ ⟨vec(b)⟩, "
        "so Σ_{t in S} rank(A_t) ≤ dim(slice) + dim(kernel) = 3 + e_A.  "
        "The row-space version gives the C-grouping bound.  "
        "The cyclic symmetry (A,B,C) → (B,C^T,A^T) preserves the tensor and transfers "
        "the A-split argument to B-split and C-split."
    ),
    "connection_to_pinned_proof": (
        "At e_A=0 (length-20 forced profile), three rank-3 A-factors each occupy a full "
        "3-dimensional B-slice. Direct-sum requires these slices to be distinct, hence "
        "three distinct B values that no other term may share. This gives a transparent "
        "reading of the existing saturation endpoint without changing the released proof."
    ),
    "rank22_application": (
        "At e_A=0 for length 22: the A-col constraint Σ_{t:B_t=b} rank(A_t) ≤ 3 "
        "forbids two rank-2 A-factors from sharing a B value (sum=4>3), "
        "and the single rank-3 factor (profile 18,3,1) must have a unique B value. "
        "This is a solver-free B/C-side pruning constraint from A-side data alone, "
        "exactly the coupling that analysis showed occupation-only exclusion was missing."
    ),
    "excess_one_note": (
        "At e_A=1 the B-sharing cap becomes 4. A rank-3 A-factor can share B with a rank-1 factor "
        "(sum=4), but not with a rank-2 factor (sum=5>4). Two rank-2 factors can share B (sum=4). "
        "This already constrains the unique length-21 residual family more than the pairwise "
        "rank tests that analysis showed were insufficient."
    ),
    "strategist_conjecture_correction": (
        "The pairwise excess-one conditions are genuinely insufficient (analysis witnesses), "
        "and the 'at most e+1 invertible factors at excess e' conjecture cannot be reached "
        "through pairwise rank inequalities. The B/C-sharing constraint is a matroid-type "
        "independence condition on subspaces col(A_t) ⊗ ⟨vec(B_t)⟩, not decomposable into "
        "two-term inequalities. Moreover, pairwise inequalities become vacuous for 3×3 matrices "
        "once e ≥ 3, which is where verified rank-23 schemes live."
    )
}

outf = OUT / "bsharing_constraint_check.json"
with open(outf, 'w') as f:
    json.dump(result, f, indent=2)

print(f"\n{'✓' if all_six_ok else '✗'} ALL SIX CONSTRAINTS: {'PASS' if all_six_ok else 'FAIL'}")
print(f"Output: {outf}")
print(json.dumps({"ok": all_six_ok, "out": str(outf)}, indent=2))
