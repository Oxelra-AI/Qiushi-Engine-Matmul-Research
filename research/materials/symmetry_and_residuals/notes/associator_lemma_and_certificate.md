# Associator bound for cubic Waring rank (the Hessian commutator lemma)

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Statement

**Theorem (Strassen-Hessian commutator bound).** Let V be an n-dimensional vector space over a field of characteristic ≠ 2, 3. Let R ∈ Sym³(V*) be a cubic form. Suppose p ∈ V satisfies K := (1/6) Hess_R(p) is nondegenerate as a symmetric bilinear form. Define the Hessian endomorphism

  H_X := K⁻¹ · (1/6) Hess_R(X).

(The formula H_X = K⁻¹ S_X is the correct coordinate-free definition; the transpose S_X K⁻¹ differs by K-conjugation but gives the same rank, traces, and Φ.)

Then:

(a) H_p = Id.

(b) H_X is K-self-adjoint for all X: K(H_X(Y), Z) = K(Y, H_X(Z)).

(c) The commutator C(X,Y) := [H_X, H_Y] satisfies KC + C^T K = 0 (K-skew-symmetric). Equivalently Ω:=KC is an ordinary skew-symmetric form. Since K is invertible, rank(C)=rank(Ω), so the rank is even. Spectral formulas for C require care when K is indefinite.

(d) If R = Σ_{i=1}^k ρ_i ℓ_i³ is any Waring decomposition (ℓ_i ∈ V*), then

  **rank([H_X, H_Y]) ≤ 2 max(0, k - n)**

for all X, Y ∈ V.

(e) Put Ω(X,Y) := K C(X,Y), an ordinary skew-symmetric bilinear form. The exact rank-≤2 condition is that **all 4×4 Pfaffians of Ω vanish**. The scalar

  Φ(X,Y) := 2 tr(C⁴) - tr(C²)²

satisfies the safe implication
- **rank(C) ≤ 2 ⟹ Φ = 0**, because rank(C)=rank(Ω)≤2 forces all degree-4 skew invariants to vanish;
- therefore **Φ ≠ 0 ⟹ rank(C) ≥ 4**, the useful one-directional certificate.

For indefinite K, the converse can fail: nilpotent or non-semisimple K-skew operators can have rank > 2 with Φ = 0. Thus Φ is a compact certificate of non-rank-2, not a complete equation for the rank-≤2 locus; the 4×4 Pfaffians of Ω are the exact equations. (Also, tr(C³)=0 is automatic for K-skew-symmetric C and carries no information.)

(f) [H_X, H_Y] = 0 for all X,Y iff the product X * Y := H_X(Y) is **associative**. This does NOT force k = n; redundant summands or non-semisimple Frobenius algebras can give k > n with associativity.

## Proof sketch

**(b)** K = S_p is symmetric. S_X = (1/6) Hess_R(X) is symmetric (Hessian bilinear form). With the column-vector convention used here, H_X = K⁻¹ S_X and hence K H_X = S_X and H_X^T K = S_X; this is the K-self-adjointness statement. The row/transpose convention S_X K⁻¹ is K-conjugate and has the same ranks and trace invariants, but it should not be mixed into this derivation.

**(c)** From (b): K[H_X, H_Y] = K H_X H_Y − K H_Y H_X = S_X H_Y − S_Y H_X, which is skew: (K[H_X,H_Y])^T = H_Y^T S_X − H_X^T S_Y = -(K[H_X,H_Y]). Thus Ω=K[H_X,H_Y] is an ordinary skew form; its rank is even, and since K is invertible the commutator has the same rank.

**(d)** Let A be the n × k matrix of coefficient vectors, D = diag(ρ_i ℓ_i(p)). Then K = A D A^T and S_X = A D_x A^T where (D_x)_{ii} = ρ_i ℓ_i(X). Set M = A^T K⁻¹ A. Then M D M = M (idempotent relation from K = ADA^T). Writing ker(A^T) = span{t_1,...,t_m} with m = k - n, one obtains

  M = D⁻¹ − Σ_{α=1}^m c_α ĥ_α ĥ_α^T,   ĥ_α = D⁻¹ t_α.

Since diagonal matrices commute, the D⁻¹ term cancels in the commutator:

  [H_X, H_Y] = A(D_x M D_y − D_y M D_x) A^T K⁻¹ = −Σ_α c_α (A G_α(X)) ∧ (A G_α(Y)) K⁻¹

where G_α(X) = D_x ĥ_α. Each rank-2 wedge product contributes at most 2 to the rank, yielding rank ≤ 2m = 2(k-n).

**(e)** Since Ω=KC is skew-symmetric and K is invertible, rank(C)=rank(Ω). A skew form has rank ≤2 exactly when its exterior square vanishes, equivalently when every 4×4 Pfaffian of Ω is zero. The scalar Φ is one invariant consequence of these Pfaffians; it is safe as a nonzero certificate, but not as a complete equation under indefinite K.

**(f)** With unit p, [H_X, H_Y] = 0 for all X,Y is equivalent to associativity of the commutative product X*Y:=H_X(Y). Nonminimal Waring expressions or non-semisimple Frobenius algebras can still have more than n displayed summands, so commutator vanishing should not be stated as equivalent to k=n without additional minimality and semisimplicity hypotheses.

## Normal form for k = n + 1

When m = 1, there is a unique relation t with At = 0. The commutator becomes:

  [H_X, H_Y] = −c · (AG(X)) ∧ (AG(Y)) · K⁻¹,    G(X) = D_x D⁻¹ t.

This has rank exactly 2 for generic (X,Y) (when G(X), G(Y) are independent).

**The span of all commutators** in this nonzero-weight normal form is Λ²(W) where W = span{a_i : t_i ≠ 0}. Elements of Λ²(W) have rank ≤ 2 iff dim W ≤ 3. For generic k = n+1 with all ℓ_i(p) nonzero, dim W = n and Λ²(W) has elements of rank up to n−1 (even). So the **individual** commutators have rank ≤ 2, but the **span** has elements of rank up to n−1.

If a k=n+1 decomposition has one summand with ℓ_i(p)=0, the D⁻¹ formula is not applicable. In that case the other n summands already give a nondegenerate basis for K, and the commutators still have a common-factor form Ω(X,Y)=b^♭∧q_{X,Y}; consequently the pointwise rank≤2 and common-pencil equation Ω(X,Y)∧Ω(X,Z)=0 remain necessary. But the dimension of the full commutator span can then be values such as dim(b^♭∧U), so span dimension alone is not an unconditional obstruction.

CRITICAL: bounded-rank classification of the linear span L is not the same as the pointwise Waring-rank condition. The Waring-rank condition forces individual commutators to rank ≤ 2 and the common-pencil equations, but does NOT force the whole span L to have upper rank 2. These are different conditions.

## BILR Pfaffian certificate

**Corollary.** The BILR residual cubic on gl₃ (n = 9, k = 11 cubes) has Φ(X₁, X₂) ≠ 0 at the integer directions:

  X₁ = (3, 0, 1; 3, −1, 1; 1, 3, −2),   X₂ = (−1, 3, −1; −1, 1, 0; −1, 2, 1).

Exact values (for C = [6S_{X₁}, 6S_{X₂}] = 36[S_{X₁}, S_{X₂}]):
- tr(C²) = −393,984
- tr(C³) = 0 (automatic)
- tr(C⁴) = 10,427,056,128
- Φ = −134,369,280,000 = −2¹⁵ · 3⁸ · 5⁴
- rank(C) = 4 mod 65521, 100003, 32003

Scaling to the true commutator [S_{X₁}, S_{X₂}]:
- Φ_true = Φ / 36⁴ = −80,000 = −2⁷ · 5⁴
- The nonzero value, not a positive-definite spectral interpretation, is the invariant certificate used here.

This proves the BILR residual has **Waring rank ≥ 11**, independently of the Koszul-Young flattening rank 722 from analysis. Combined with the explicit 11-cube decomposition, the BILR residual has Waring rank exactly 11.

## Intrinsic K and universality

K = (1/6) Hess_R(p) is **intrinsic to R**. When all ℓ_i(p) are nonzero, setting μ_i = ℓ_i/ℓ_i(p) gives K = Σ w_i μ_i⊗μ_i. If a low-rank decomposition contains a summand with ℓ_i(p)=0, one treats it separately as a zero-weight summand; for k≤n+1 there can be at most one such summand and the pointwise rank≤2/common-pencil necessary condition still holds. Thus the Strassen-Hessian obstruction applies to any candidate decomposition of the fixed R, not just to the displayed one. The BILR certificate proves that no Waring decomposition with ≤10 terms exists for R_BILR.

## Scope for (10,4) cyclic exclusion

The certificate is for the **fixed BILR residual cubic**. A different internal frame choice for the four exterior planes gives a different residual cubic. A finite-field frame scan only shows that sampled frames did not hit the algebraic locus forced by a ten-cube residual; it is not a nonexistence argument.

**analysis correction.** Do not try to prove that one scalar polynomial Φ(X₁,Y₁;frame) has no zeros on SL₃⁴: on the actual SL₃⁴ frame variety, a regular function with no zeros would be a unit, and the relevant coordinate rings have only constant units; in any localized chart this must be rechecked. In any case, sampled finite fields cannot exclude the special closed locus where a rank-22 cyclic algorithm would have to live. The exact equations are the 4×4 Pfaffians of Ω=K[H_X,H_Y] for all relevant pairs X,Y, together with the exterior equation Σ u_j∧v_j∧w_j=ω.

analysis calibrated the reduced-pair idea on the BILR component. For each split {i,j}|{k,l}, taking X,Y spanning (P_i+P_j)^⊥∩sl₃ kills the corrections from P_i and P_j and makes the commutator depend only on the other two frames. At the BILR identity frame all six reduced commutators are zero, while the Jordan-only commutator has rank 4; hence these reduced-pair equations are inactive on the BILR frame and should not be the next heavy elimination target. The useful exact next equations are the full Pfaffians/common-pencil conditions for symbolic frames, not single-pair scalar scans.

**Span-dimension caution.** analysis computed the commutator span dimension at BILR as 4. In the all-nonzero-weight k=n+1 normal form the span is Λ²(U) of dimension d(d-1)/2, so 4 would obstruct such a normal form. However, a hypothetical 10-cube decomposition with one ℓ_i(p)=0 can have a common-factor span of dimension 4. Therefore span dimension 4 is useful structural evidence but not an unconditional third proof; the unconditional fixed-BILR lower bound comes from the actual rank-4/Pfaffian/common-pencil certificates and the Koszul--Young flattening.

## Literature context (review correction)

The rank bound rank([H_X, H_Y]) ≤ 2(k-n) is a specialization of the **Strassen commutator lower bound** to symmetric cubics, not primarily a Jennrich theorem. Jennrich's contribution concerns the k = n case (simultaneous diagonalization from commutator vanishing). The K-self-adjointness, K-skewness of commutators, even rank, and vanishing odd traces are standard linear algebra of symmetric specialization.

The BILR integer certificate and its connection to the pure-cyclic rank-22 problem appear to be new, but the underlying rank bound mechanism should be attributed to Strassen's framework. A proper literature check of Strassen-type equations for Veronese/secant varieties and cubic Hessian invariants is needed before claiming originality of the lemma statement.

## Files
- [pfaffian_certificate.py](../code/pfaffian_certificate.py): computation script
- [pfaffian_certificate_and_scan.json](../results/pfaffian_certificate/pfaffian_certificate_and_scan.json): certificate
- This file: the lemma and certificate note
