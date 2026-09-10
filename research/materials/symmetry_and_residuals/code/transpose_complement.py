#!/usr/bin/env python3
"""analysis: transpose complementary sector for tau(X,Y,Z)=(X^T,Z^T,Y^T).

This script fixes the coefficient convention, verifies the Gram/complement split
against the naive 27-term scheme, builds the 3 x 36 complementary target
T_anti(A;Y,Z)=tr(A Y Z) for A skew-symmetric, and studies the entry condition:
minimum number m of tau-free orbits, i.e. decomposable tau-skew products
    v(Y) w(Z) - w^T(Y) v^T(Z),
whose span contains the 3-dimensional target skew-form space.

The output is exact linear algebra plus numerical search diagnostics only; failed
numerical searches are not lower bounds.
"""
from __future__ import annotations
import json
from pathlib import Path
import itertools
import numpy as np

SESSION = Path(__file__).resolve().parents[1]
OUT = SESSION / "data" / "transpose_complement"
OUT.mkdir(parents=True, exist_ok=True)

# Coordinates for W = variables Y_{row, col}.  The corresponding Z variable
# under tau is Z_{col,row}.  index(row, col) = 3*row + col.
def idx(i: int, k: int) -> int:
    return 3*i + k

# Symmetric and exterior monomial indices on 9 variables.
def sym_idx(a: int, b: int, n: int = 9) -> int:
    if a > b:
        a, b = b, a
    return a * n - a * (a - 1) // 2 + (b - a)

def wedge_pairs(n: int = 9):
    return [(a, b) for a in range(n) for b in range(a+1, n)]
WEDGE_PAIRS = wedge_pairs(9)
WEDGE_INDEX = {p:i for i,p in enumerate(WEDGE_PAIRS)}

# X bases: symmetric and skew coefficient matrices.  Pairing is entrywise
# <u,X>=sum_ij u_ij X_ij.  With this convention <u^T,A> = -<u,A> for A^T=-A.
SYM_PAIRS = [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
SKEW_PAIRS = [(0,1),(0,2),(1,2)]

def sym_basis():
    B=[]
    for i,j in SYM_PAIRS:
        M=np.zeros((3,3), dtype=int)
        M[i,j]=1
        if i!=j: M[j,i]=1
        B.append(M)
    return B

def skew_basis():
    B=[]
    for i,j in SKEW_PAIRS:
        M=np.zeros((3,3), dtype=int)
        M[i,j]=1; M[j,i]=-1
        B.append(M)
    return B
SYM_BASIS=sym_basis(); SKEW_BASIS=skew_basis()

def lin_from_matrix_on_Y(M: np.ndarray) -> np.ndarray:
    """Linear form l_M(Y)=sum M_ij Y_ij as length-9 vector."""
    return np.array(M, dtype=complex).reshape(9)

def lin_from_wT_on_Y(W: np.ndarray) -> np.ndarray:
    """Linear form l_{W^T}(Y) = sum W^T_ij Y_ij."""
    return np.array(W.T, dtype=complex).reshape(9)

def product_sym_vec(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Symmetric coefficient vector for (a.x)(b.x), length 45."""
    v=np.zeros(45, dtype=complex)
    for i in range(9):
        for j in range(i,9):
            if i==j:
                v[sym_idx(i,j)] = a[i]*b[j]
            else:
                v[sym_idx(i,j)] = a[i]*b[j] + a[j]*b[i]
    return v

def wedge_vec(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    """Exterior coefficient vector for a(x)b(z)-b(x)a(z), length 36."""
    v=np.zeros(36, dtype=complex)
    for t,(i,j) in enumerate(WEDGE_PAIRS):
        v[t] = a[i]*b[j] - a[j]*b[i]
    return v

def skew_matrix_from_wedge(v: np.ndarray) -> np.ndarray:
    M=np.zeros((9,9), dtype=complex)
    for coeff,(i,j) in zip(v, WEDGE_PAIRS):
        M[i,j]=coeff; M[j,i]=-coeff
    return M

def gram_target() -> np.ndarray:
    """6 x 45 Gram sector: G_jk(Y)=sum_l Y_jl Y_kl."""
    G=np.zeros((6,45), dtype=complex)
    for r,(j,k) in enumerate(SYM_PAIRS):
        coeff = 1 if j == k else 2  # basis E_jk+E_kj gives 2 G_jk in tr(SYY^T)
        for ell in range(3):
            a=idx(j,ell); b=idx(k,ell)
            G[r, sym_idx(a,b)] += coeff
    return G

def anti_target() -> np.ndarray:
    """3 x 36 target skew forms for tr(A Y Z), with Z_{k,i} identified with Y_{i,k}."""
    T=np.zeros((3,36), dtype=complex)
    # tr(A Y Z) = sum_{i,j,k} A_{i,j} Y_{j,k} Z_{k,i}.
    # Under tau identification, Z_{k,i} pairs with coordinate x_{i,k}; Y_{j,k}=x_{j,k}.
    # For skew basis A_ab = E_ab - E_ba, this gives x_{b,k} z_{a,k} - x_{a,k} z_{b,k}
    # = -(x_{a,k} z_{b,k} - x_{b,k} z_{a,k}) depending on pair ordering.
    for r,A in enumerate(SKEW_BASIS):
        M=np.zeros((9,9), dtype=complex)  # coefficient y_index, z_identified_index
        for i in range(3):
            for j in range(3):
                if A[i,j]==0: continue
                for k in range(3):
                    y=idx(j,k)
                    z=idx(i,k)
                    M[y,z] += A[i,j]
        # Since target is tau-invariant and A is skew, M is skew-symmetric in identified vars.
        if np.max(np.abs(M + M.T)) != 0:
            raise RuntimeError("anti slice not skew; convention bug")
        for t,(i,j) in enumerate(WEDGE_PAIRS):
            T[r,t] = M[i,j]
    return T

G_TARGET=gram_target(); A_TARGET=anti_target()

def rank_complex(M, tol=1e-9):
    if M.size==0: return 0
    s=np.linalg.svd(np.asarray(M, dtype=complex), compute_uv=False)
    return int((s>tol).sum())

def flattening_ranks_anti():
    # Tensor shape A(3), Y(9), Z(9), skew matrix coefficients.
    T=np.zeros((3,9,9), dtype=int)
    for r,row in enumerate(A_TARGET):
        M=skew_matrix_from_wedge(row)
        T[r]=np.rint(M.real).astype(int)
    # flatten A | YZ
    rA=np.linalg.matrix_rank(T.reshape(3,81))
    rY=np.linalg.matrix_rank(np.transpose(T,(1,0,2)).reshape(9,27))
    rZ=np.linalg.matrix_rank(np.transpose(T,(2,0,1)).reshape(9,27))
    slice_ranks=[]
    for coeff in [(1,0,0),(0,1,0),(0,0,1),(1,2,3),(2,-1,1)]:
        M=sum(coeff[i]*T[i] for i in range(3))
        slice_ranks.append({"coeff": coeff, "rank": int(np.linalg.matrix_rank(M))})
    return {"A_flattening_rank": int(rA), "Y_flattening_rank": int(rY),
            "Z_flattening_rank": int(rZ), "slice_ranks": slice_ranks,
            "conciseness_lower_m": int((max(rY,rZ)+1)//2)}

def naive_27_terms():
    terms=[]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                u=np.zeros((3,3), dtype=int); u[i,j]=1
                v=np.zeros((3,3), dtype=int); v[j,k]=1
                w=np.zeros((3,3), dtype=int); w[k,i]=1
                terms.append((u,v,w))
    return terms

def tau_image(term):
    u,v,w=term
    return (u.T.copy(), w.T.copy(), v.T.copy())

def term_key(term):
    return tuple(np.concatenate([term[0].reshape(9),term[1].reshape(9),term[2].reshape(9)]).tolist())

def check_naive_tau_split():
    terms=naive_27_terms()
    pos={term_key(t):i for i,t in enumerate(terms)}
    seen=set(); fixed=[]; free=[]
    for i,t in enumerate(terms):
        if i in seen: continue
        j=pos[term_key(tau_image(t))]
        if i==j:
            fixed.append(i); seen.add(i)
        else:
            free.append((i,j)); seen.add(i); seen.add(j)
    # Accumulate Gram and anti sectors from fixed/free orbit formulas.
    gram_acc=np.zeros((6,45), dtype=complex)
    anti_acc=np.zeros((3,36), dtype=complex)
    for i in fixed:
        u,v,w=terms[i]
        # fixed means u symmetric, w=v^T. Contribution on fixed locus: <u,S> * l_v(Y)^2.
        vu=lin_from_matrix_on_Y(v)
        q=product_sym_vec(vu, vu)
        for r,S in enumerate(SYM_BASIS):
            gram_acc[r] += np.sum(u*S) * q
        # anti contribution should vanish.
        for r,A in enumerate(SKEW_BASIS):
            anti_acc[r] += np.sum(u*A) * wedge_vec(vu, lin_from_wT_on_Y(w))
    for i,j in free:
        u,v,w=terms[i]
        # Use representative plus its tau image. On fixed locus the product appears with u_sym.
        a=lin_from_matrix_on_Y(v)
        b=lin_from_wT_on_Y(w)  # l_{w^T}(Y)
        q=product_sym_vec(a,b)
        for r,S in enumerate(SYM_BASIS):
            # orbit contribution <u,S> ab + <u^T,S> ba = 2 <u_sym,S> ab; with entrywise S symmetric, <u^T,S>=<u,S>
            gram_acc[r] += (np.sum(u*S) + np.sum(u.T*S)) * q
        kw=wedge_vec(a,b)
        for r,A in enumerate(SKEW_BASIS):
            # <u,A> [a(Y)b(Z)-b(Y)a(Z)] because <u^T,A>=-<u,A>
            anti_acc[r] += np.sum(u*A) * kw
    return {
        "fixed_count": len(fixed), "free_orbit_count": len(free),
        "fixed_indices": fixed, "free_orbits_first5": free[:5],
        "gram_matches_target": bool(np.allclose(gram_acc, G_TARGET)),
        "anti_matches_target": bool(np.allclose(anti_acc, A_TARGET)),
        "max_gram_error": float(np.max(np.abs(gram_acc-G_TARGET))),
        "max_anti_error": float(np.max(np.abs(anti_acc-A_TARGET))),
        "pairing_convention": "entrywise <u,X>=sum u_ij X_ij; tau term is (u^T,w^T,v^T); for A^T=-A, <u^T,A>=-<u,A>",
    }

def canonical_nine_anti_terms():
    """The obvious 9 decomposable wedges: for each row pair and column k."""
    terms=[]
    coeff=np.zeros((3,9), dtype=complex)
    col=0
    for r,(i,j) in enumerate(SKEW_PAIRS):
        # anti_target sign may be - e_i,k wedge e_j,k depending convention; use solve later.
        for k in range(3):
            a=np.zeros(9); b=np.zeros(9)
            a[idx(i,k)] = 1; b[idx(j,k)] = 1
            terms.append(wedge_vec(a,b))
            col += 1
    K=np.array(terms).T # 36 x 9
    # Check containment and compute coefficient matrix expressing A_TARGET rows.
    aug=np.column_stack([K, A_TARGET.T])
    return {"rank_terms": rank_complex(K), "rank_augmented_with_target": rank_complex(aug),
            "contains_target": rank_complex(K)==rank_complex(aug)}

def gram_polarization_free_wedges():
    """Six free-product wedges from the analysis row-norm polarization.

    For row-combination h in [e0,e1,e2,e0+e1,e0+e2,e1+e2], use
    (h col0 + i h col1) and (h col0 - i h col1).  The square on col2 is fixed,
    not a free orbit.  Compute how much of the anti target lies in their span.
    """
    I=1j
    hs=[]
    for subset in [(0,), (1,), (2,), (0,1), (0,2), (1,2)]:
        h=np.zeros(3, dtype=complex)
        for s in subset: h[s]=1
        hs.append((subset,h))
    wedges=[]
    for subset,h in hs:
        a=np.zeros(9, dtype=complex); b=np.zeros(9, dtype=complex)
        for row in range(3):
            a[idx(row,0)] += h[row]
            a[idx(row,1)] += I*h[row]
            b[idx(row,0)] += h[row]
            b[idx(row,1)] += -I*h[row]
        wedges.append(wedge_vec(a,b))
    K=np.array(wedges).T
    rK=rank_complex(K)
    r_aug=rank_complex(np.column_stack([K, A_TARGET.T]))
    # Project into GL(U)xGL(C) components for diagnosis: target component Lambda2U Sym2C vs Sym2U Lambda2C.
    # Here simply report that target not contained if rank_aug>rank.
    return {"six_polarization_free_wedge_rank": rK,
            "rank_with_anti_target": r_aug,
            "anti_target_contained": rK==r_aug,
            "anti_target_new_dimensions_mod_six": r_aug-rK}

# Numerical anti decomposition search; used only as a route diagnostic.
def anti_residual_vector(vars, m):
    # variables: P(m,9), Q(m,9), C(3,m)
    off=0
    P=vars[off:off+m*9].reshape(m,9); off+=m*9
    Q=vars[off:off+m*9].reshape(m,9); off+=m*9
    C=vars[off:off+3*m].reshape(3,m)
    K=np.array([wedge_vec(P[t], Q[t]) for t in range(m)])  # m x 36
    R=C @ K - A_TARGET.real
    return R.reshape(-1)

def run_numerical_search(max_restarts=20, seed=0):
    try:
        from scipy.optimize import least_squares
    except Exception as e:
        return {"available": False, "error": repr(e)}
    rng=np.random.default_rng(seed)
    results={"available": True, "note": "heuristic real least_squares; failures are not lower bounds", "by_m": {}}
    # Exact 9-term initialization for sanity.
    for m in [5,6,7,8,9]:
        best=1e99; best_norm=None; succ=0
        trials = max_restarts if m<9 else min(5, max_restarts)
        for t in range(trials):
            if m==9 and t==0:
                # initialize at canonical exact terms and solve coefficients roughly
                P=np.zeros((m,9)); Q=np.zeros((m,9)); C=np.zeros((3,m))
                c=0
                for r,(i,j) in enumerate(SKEW_PAIRS):
                    for k in range(3):
                        P[c,idx(i,k)]=1; Q[c,idx(j,k)]=1
                        # sign from target row: solve by least squares below; set -1 guess.
                        C[r,c]=-1
                        c+=1
                x0=np.concatenate([P.ravel(),Q.ravel(),C.ravel()])
            else:
                scale=0.5
                x0=rng.normal(scale=scale, size=18*m+3*m)
            res=least_squares(lambda x: anti_residual_vector(x,m), x0, max_nfev=20000,
                              ftol=1e-12, xtol=1e-12, gtol=1e-12, verbose=0)
            val=float(np.linalg.norm(res.fun))
            norm=float(np.linalg.norm(res.x))
            if val<best:
                best=val; best_norm=norm
            if val<1e-8:
                succ+=1
                # Save first successful parameters for possible exactification.
                if f"m{m}_success_path" not in results:
                    pth=OUT/f"anti_numeric_m{m}_candidate.npy"
                    np.save(pth, res.x)
                    results[f"m{m}_success_path"] = str(pth.relative_to(SESSION))
                break
        results["by_m"][str(m)]={"best_residual_norm": best, "best_variable_norm": best_norm,
                                  "successes": succ, "trials": trials}
    return results


def main():
    out={}
    out["tau_pairing_naive27_check"] = check_naive_tau_split()
    out["anti_target_matrix"] = {
        "basis_skew_pairs": SKEW_PAIRS,
        "wedge_pairs": WEDGE_PAIRS,
        "target_rows_integer": [[int(round(x.real)) for x in row] for row in A_TARGET],
    }
    out["anti_flattening_and_slice_ranks"] = flattening_ranks_anti()
    out["canonical_9_term_upper_bound"] = canonical_nine_anti_terms()
    out["canonical_gram_polarization_free_wedges"] = gram_polarization_free_wedges()
    out["numerical_search"] = {"skipped": True, "reason": "analysis follows the warning: do not optimize a 378-residual; the useful test is exact linear feasibility once (v,w) are fixed."}
    path=OUT/"transpose_complement_entry.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({
        "naive27": out["tau_pairing_naive27_check"],
        "flattening": out["anti_flattening_and_slice_ranks"],
        "anti_9_upper": out["canonical_9_term_upper_bound"],
        "polarization_six": out["canonical_gram_polarization_free_wedges"],
        "numeric": out["numerical_search"],
        "saved": str(path),
    }, indent=2))

if __name__ == "__main__":
    main()
