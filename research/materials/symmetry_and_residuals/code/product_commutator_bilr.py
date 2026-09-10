#!/usr/bin/env python3
"""
analysis: product-form Hessian commutator instrument for pure-cyclic (10,4).

This script avoids symbolic cubic construction.  For a traceless free-orbit residual

    R(X) = tr(X^3) - 3 sum_j l_{u_j}(X) l_{v_j}(X) l_{w_j}(X),

with trace pairing l_A(X)=tr(A X), the normalized Hessian endomorphism
H_X=(1/6) Hess_R(X) K^{-1} is multiplication by the commutative product

    H_X(Y) = (XY+YX)/2
      - 1/2 sum_j [ (v_j(X)w_j(Y)+w_j(X)v_j(Y)) u_j
                  + (u_j(X)w_j(Y)+w_j(X)u_j(Y)) v_j
                  + (u_j(X)v_j(Y)+v_j(X)u_j(Y)) w_j ].

The script uses the integer-scaled operator H2=2H.  The stored BILR matrices L
are converted to trace-pairing gradients A=L^T, since existing files use
ell_L(X)=tr(L^T X).  It verifies this product formula against the 11-cube BILR
residual Hessian, computes the BILR commutator image space, compression data, and
cheap scalar rank<=2 obstructions.
"""

from pathlib import Path
import json
import random
import sympy as sp

WS = Path(__file__).resolve().parent.parent
OUT = WS / "data" / "product_commutator"
OUT.mkdir(parents=True, exist_ok=True)

# -----------------------------------------------------------------------------
# Basic gl_3 linear algebra
# -----------------------------------------------------------------------------

def E(i, j):
    M = sp.zeros(3, 3)
    M[i, j] = 1
    return M

basis = [E(i, j) for i in range(3) for j in range(3)]
basis_names = [f"E{i}{j}" for i in range(3) for j in range(3)]

K = sp.Matrix([[sp.trace(basis[a] * basis[b]) for b in range(9)] for a in range(9)])
assert K.det() == -1
assert K * K == sp.eye(9)

# Coordinates use X=sum x_a basis[a].
def vec_to_mat(x):
    M = sp.zeros(3, 3)
    for a, xa in enumerate(x):
        M += sp.Rational(xa) * basis[a]
    return M

def mat_to_vec(M):
    return sp.Matrix([sp.simplify(M[i, j]) for i in range(3) for j in range(3)])

def ell(A, X):
    """Trace-pairing linear form l_A(X)=tr(A X)."""
    return sp.trace(A * X)

def mat_from_json(M):
    return sp.Matrix([[sp.Rational(M[i][j]) for j in range(3)] for i in range(3)])

# -----------------------------------------------------------------------------
# Load BILR data and choose the convention that matches the cube residual.
# -----------------------------------------------------------------------------
with open(WS / "data" / "ballard_z4_cyclic" / "ballard_z4_cyclic_scheme.json") as f:
    scheme = json.load(f)

stored_cubes = [mat_from_json(M) for M in scheme["cubes"]]
stored_reps = scheme["free_orbit_representatives"]

# Previous convention: stored L defines ell_L(X)=tr(L^T X).  Under l_A=tr(A X),
# the gradient is A=L^T.  Since traces are +-1 for BILR, mu=lambda/c equals
# c*lambda coefficient-wise.
cube_gradients = [L.T for L in stored_cubes]
cube_traces = [sp.trace(A) for A in cube_gradients]
assert all(c in (sp.Integer(1), sp.Integer(-1)) for c in cube_traces)
# lambda coefficient row mu_i, normalized by c_i; because c_i=+-1 this is c_i*lambda.
mu_rows = []
weights = []
for A, c in zip(cube_gradients, cube_traces):
    lam = sp.Matrix([ell(A, B) for B in basis])
    mu_rows.append(c * lam)  # lambda/c = c*lambda for c^2=1
    weights.append(c**3)

S_moment = sp.zeros(9, 9)
for w, mu in zip(weights, mu_rows):
    S_moment += w * (mu * mu.T)
# S_moment should be K, because K(H_I Y,Z)=K(Y,Z) and H_I=Id.
moment_ok = sp.simplify(S_moment - K) == sp.zeros(9, 9)

# Free-orbit gradients under l_A=tr(A X).  Test both stored and transpose convention
# below; the expected correct one is transpose.
def tracefree(M):
    return sp.simplify(M - sp.trace(M) / 3 * sp.eye(3))

def load_free_triples(use_transpose=True):
    triples = []
    for rep in stored_reps:
        triple = []
        for key in ["U", "V", "W"]:
            L = tracefree(mat_from_json(rep[key]))
            A = L.T if use_transpose else L
            triple.append(A)
        triples.append(tuple(triple))
    return triples

# -----------------------------------------------------------------------------
# Hessian operators: cube form and product form.
# -----------------------------------------------------------------------------

def H2_from_cubes(x):
    """H2=2*(1/6 Hess_R(x)K^{-1}) from the 11-cube residual, column convention.

    If S_x=sum_i w_i mu_i(x) mu_i mu_i^T, then H_x has coordinate matrix K*S_x.
    """
    x = sp.Matrix([sp.Rational(v) for v in x])
    S = sp.zeros(9, 9)
    for w, mu in zip(weights, mu_rows):
        S += w * (mu.dot(x)) * (mu * mu.T)
    return sp.simplify(2 * K * S)


def H2_product(x, triples):
    """H2=2H from the closed product formula.  Columns are H2_X(basis[j])."""
    X = vec_to_mat(x)
    cols = []
    for Y in basis:
        out = X * Y + Y * X
        for U, V, W in triples:
            uX, vX, wX = ell(U, X), ell(V, X), ell(W, X)
            uY, vY, wY = ell(U, Y), ell(V, Y), ell(W, Y)
            out -= (vX*wY + wX*vY) * U
            out -= (uX*wY + wX*uY) * V
            out -= (uX*vY + vX*uY) * W
        cols.append(mat_to_vec(out))
    return sp.Matrix.hstack(*cols)

# Compare conventions using several directions.
test_dirs = [
    [1,0,0,0,1,0,0,0,1],
    [3,0,1,3,-1,1,1,3,-2],
    [-1,3,-1,-1,1,0,-1,2,1],
    [0,1,2,-1,0,3,2,-2,1],
]
convention_tests = []
for use_transpose in [True, False]:
    triples = load_free_triples(use_transpose=use_transpose)
    max_abs = sp.Integer(0)
    mismatch_entries = 0
    for x in test_dirs:
        diff = sp.simplify(H2_product(x, triples) - H2_from_cubes(x))
        vals = list(diff)
        mismatch_entries += sum(1 for v in vals if v != 0)
        if vals:
            max_abs = max(max_abs, max(abs(v) for v in vals))
    convention_tests.append({
        "free_gradients_are_stored_transposes": use_transpose,
        "mismatch_entries_over_test_directions": int(mismatch_entries),
        "max_abs_mismatch": str(max_abs),
    })

triples = load_free_triples(use_transpose=True)
product_formula_matches_cubes = convention_tests[0]["mismatch_entries_over_test_directions"] == 0
if not product_formula_matches_cubes:
    raise RuntimeError("Expected transpose convention did not match BILR cube Hessian")

# -----------------------------------------------------------------------------
# Commutator image spaces and invariants.
# -----------------------------------------------------------------------------

def comm(A, B):
    return sp.simplify(A*B - B*A)

def rank(M):
    return int(sp.Matrix(M).rank())

def flatten(M):
    return [sp.simplify(M[i, j]) for i in range(M.rows) for j in range(M.cols)]

def image_space_data(H_mats):
    comms = []
    labels = []
    ranks = []
    for a in range(9):
        for b in range(a+1, 9):
            C = comm(H_mats[a], H_mats[b])
            comms.append(C)
            labels.append([basis_names[a], basis_names[b]])
            ranks.append(rank(C))
    span_matrix = sp.Matrix([flatten(C) for C in comms])
    span_dim = int(span_matrix.rank())
    # Fixed image space: span of all columns of all C.
    concat_cols = sp.Matrix.hstack(*comms)
    common_image_dim = int(concat_cols.rank())
    # Common kernel: intersection ker C = kernel of vertical stack.
    vertical = sp.Matrix.vstack(*comms)
    vertical_rank = int(vertical.rank())
    common_kernel_dim = 9 - vertical_rank
    return {
        "comms": comms,
        "labels": labels,
        "basis_commutator_ranks": ranks,
        "span_dim": span_dim,
        "common_image_dim": common_image_dim,
        "common_kernel_dim": common_kernel_dim,
        "vertical_rank_for_common_kernel_codim": vertical_rank,
        "max_basis_commutator_rank": max(ranks),
        "nonzero_basis_commutators": sum(1 for r in ranks if r != 0),
    }

def random_combo_rank_hist(comms, trials=200, coeff_bound=3, seed=1234):
    rng = random.Random(seed)
    hist = {}
    examples = {}
    for _ in range(trials):
        C = sp.zeros(9, 9)
        coeffs = []
        for _j, Cj in enumerate(comms):
            c = rng.randint(-coeff_bound, coeff_bound)
            coeffs.append(c)
            if c:
                C += c*Cj
        r = rank(C)
        hist[str(r)] = hist.get(str(r), 0) + 1
        examples.setdefault(str(r), coeffs)
    return hist, examples

# BILR product H2 for basis directions.
H2_bilr_basis = [H2_product([1 if i == a else 0 for i in range(9)], triples) for a in range(9)]
bilr_L = image_space_data(H2_bilr_basis)
bilr_hist, bilr_examples = random_combo_rank_hist(bilr_L["comms"], trials=200)

# Pure trace-cube calibration: H2_0(X)Y=XY+YX.
def H2_jordan(x):
    X = vec_to_mat(x)
    return sp.Matrix.hstack(*[mat_to_vec(X*Y + Y*X) for Y in basis])

H2_jordan_basis = [H2_jordan([1 if i == a else 0 for i in range(9)]) for a in range(9)]
jordan_L = image_space_data(H2_jordan_basis)
jordan_hist, jordan_examples = random_combo_rank_hist(jordan_L["comms"], trials=200)

# Certificate directions from analysis.
x1 = [3,0,1,3,-1,1,1,3,-2]
x2 = [-1,3,-1,-1,1,0,-1,2,1]
C_cert = comm(H2_product(x1, triples), H2_product(x2, triples))
cert_rank = rank(C_cert)
# Find the first nonzero 3x3 minor and also the previous rows/cols if nonzero.
first_minor = None
for rows in sp.utilities.iterables.combinations(range(9), 3):
    for cols in sp.utilities.iterables.combinations(range(9), 3):
        d = sp.Matrix(C_cert.extract(rows, cols)).det()
        if d != 0:
            first_minor = {"rows": list(rows), "cols": list(cols), "det": str(sp.factor(d))}
            break
    if first_minor:
        break
prev_rows = [1,2,3]
prev_cols = [1,2,6]
prev_det_H2_col = sp.Matrix(C_cert.extract(prev_rows, prev_cols)).det()

# Scalar rank<=2 obstructions for a traceless matrix C.
trC = sp.trace(C_cert)
trC2 = sp.trace(C_cert**2)
trC3 = sp.trace(C_cert**3)
trC4 = sp.trace(C_cert**4)
rank2_identity = sp.simplify(2*trC4 - trC2**2)
scalar_obstructions = {
    "trace_C": str(sp.factor(trC)),
    "trace_C2": str(sp.factor(trC2)),
    "trace_C3_rank_le2_requires_zero": str(sp.factor(trC3)),
    "two_trace_C4_minus_trace_C2_squared_rank_le2_requires_zero": str(sp.factor(rank2_identity)),
    "trace_C3_nonzero": bool(trC3 != 0),
    "quartic_identity_nonzero": bool(rank2_identity != 0),
}

# Compression tests for the actual BILR L and pure Jordan L.
def compression_summary(D):
    return {
        "span_dim": D["span_dim"],
        "common_image_dim": D["common_image_dim"],
        "is_image_compressed_to_dim_le2": D["common_image_dim"] <= 2,
        "common_kernel_dim": D["common_kernel_dim"],
        "is_kernel_compressed_with_common_kernel_dim_ge7": D["common_kernel_dim"] >= 7,
        "max_basis_commutator_rank": D["max_basis_commutator_rank"],
        "nonzero_basis_commutators": D["nonzero_basis_commutators"],
    }

# Literature snippets captured manually from Knowledge Request sources.
literature_context = {
    "bounded_rank_spaces": {
        "eisenbud_harris": "Vector spaces of matrices of low rank, Adv. Math. 1988, citation key \\cite{eisenbud1988vector}; retrieved metadata only in this ARTIFACT.",
        "huang_landsberg_2026_source_lines": "Knowledge object On Linear spaces of matrices bounded rank, lines 29-40 define compression spaces and state that Atkinson-Lloyd classified rank-2 spaces, with the only primitive rank-2 space the 3x3 skew-symmetric example; lines 288-295 review the compression/primitivity reduction.",
        "pazzis_theorem4_source_lines": "Pazzis classification theorem lines 106-109: large rank<=r subspaces of M_n are image- or kernel-compression spaces beyond dimension nr-r+1, with boundary alternatives. Useful for context, but not by itself sufficient for arbitrary low-dimensional L.",
    },
    "trace_cube_waring": {
        "chiantini_hauenstein_ikenmeyer_landsberg_ottaviani": "\\cite{chiantini2017polynomials}: Proposition 2.6 gives symmetric border rank of tr(X^3) on Mat_3 at least 14; Conjecture 2.8 predicts Waring rank 18 after numerical 18-summand decompositions. This calibrates that pure tr(X^3) is much harder than rank<=10 residuals.",
    }
}

result = {
    "scope": "Product-form Hessian commutator instrument for BILR traceless pure-cyclic residual on gl_3.",
    "operator_scaling": "H2=2H where H=(1/6) Hess_R(X) K^{-1}; scaling does not affect ranks or bounded-rank compression tests.",
    "basis_order": basis_names,
    "trace_form_det": str(K.det()),
    "moment_sum_w_mu_mu_equals_K": bool(moment_ok),
    "cube_traces": [str(c) for c in cube_traces],
    "cube_weights": [str(w) for w in weights],
    "convention_tests": convention_tests,
    "product_formula_matches_11cube_hessian_with_transposed_stored_free_reps": bool(product_formula_matches_cubes),
    "bilr_commutator_certificate_H2_column_convention": {
        "x1": x1,
        "x2": x2,
        "rank_over_Q": cert_rank,
        "first_nonzero_3x3_minor": first_minor,
        "rows_1_2_3_cols_1_2_6_det_in_H2_column_convention": str(sp.factor(prev_det_H2_col)),
        "scalar_rank_le2_obstructions": scalar_obstructions,
    },
    "bilr_commutator_image_space_L": compression_summary(bilr_L),
    "bilr_basis_commutator_rank_histogram": {str(r): bilr_L["basis_commutator_ranks"].count(r) for r in sorted(set(bilr_L["basis_commutator_ranks"]))},
    "bilr_random_linear_combo_rank_histogram_200_trials": bilr_hist,
    "jordan_trace_cube_commutator_image_space_calibration": compression_summary(jordan_L),
    "jordan_basis_commutator_rank_histogram": {str(r): jordan_L["basis_commutator_ranks"].count(r) for r in sorted(set(jordan_L["basis_commutator_ranks"]))},
    "jordan_random_linear_combo_rank_histogram_200_trials": jordan_hist,
    "interpretation": (
        "The closed product formula exactly reproduces the BILR 11-cube residual Hessian when stored free-rep matrices are transposed into the trace-pairing convention. "
        "At BILR, the commutator image space L is high-dimensional, has full common image and no large common kernel, and contains rank-4 operators, so it is far from a rank<=2 compression space. "
        "This strengthens the BILR residual Waring-rank certificate but does not exclude special valid (10,4) frames where all 3x3 minors of C(X,Y) vanish; those frames are precisely a possible candidate locus."
    ),
    "literature_context": literature_context,
}

out = OUT / "bilr_product_commutator_invariants.json"
with open(out, "w") as f:
    json.dump(result, f, indent=2)

print(json.dumps({
    "out": str(out),
    "product_formula_matches": product_formula_matches_cubes,
    "cert_rank_Q": cert_rank,
    "cert_trace_C3": scalar_obstructions["trace_C3_rank_le2_requires_zero"],
    "cert_rank2_quartic_identity": scalar_obstructions["two_trace_C4_minus_trace_C2_squared_rank_le2_requires_zero"],
    "bilr_L": compression_summary(bilr_L),
    "jordan_L": compression_summary(jordan_L),
}, indent=2))
