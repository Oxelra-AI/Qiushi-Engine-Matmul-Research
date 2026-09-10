# Two-sector structure, frozen-span theorem, f-parity, and deformation requirements

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Three theorems and one structural observation

### Result A: Two-sector decomposition (verified)

Under standard τ(X,Y,Z) = (X^T, Z^T, Y^T), the first slice space decomposes:

    L_1 = L_sym(6) ⊕ L_anti(3)

where L_sym = {B_{aa}, (B_{ab}+B_{ba})/2}_{a<b} and L_anti = {(B_{ab}-B_{ba})/2}_{a<b}.

In characteristic ≠ 2, the τ-containment L_1 ⊆ span(terms) decomposes exactly:
- Anti sector: L_anti ⊆ span{v_j ∧ w_j} (free orbit bivectors)
- Sym sector: L_sym ⊆ span{fixed terms} + span{free symmetric products}

For skeleton (f,m) with r = f + 2m = 22: 198 total unknowns (9f + 18m).
This decomposition governs the search: the anti sector constrains the free pairs alone, 
the sym sector couples them to the fixed terms.

### Result B: Frozen-Laderman-free-span compatibility (characteristic-zero theorem)

Over Q(i), the compatibility variety for τ-fixed rank-one generators in F + L_1 has:
- Projective dimension 0
- Projective degree 3
- Exactly 3 Q(i)-rational points (charts x2, x5, x8)

Matches the F_5 result exactly (analysis: degree 3, charts x2, x5, x8).

**Theorem**: Over any algebraically closed field K ⊇ Q(i) (in particular, over C), there
are exactly 3 (counted with multiplicity) projective τ-fixed rank-one generators compatible
with the transported Laderman free span. Since a (6,8) completion requires 6 such generators
spanning a 6-dimensional quotient, and 3 < 6, no τ-invariant rank-22 scheme shares the
transported Laderman eight free orbits.

**Corollary**: Any τ-invariant rank-22 decomposition must move at least one of Laderman's
eight free orbits.

The bilinear variety (general rank-one, not τ-fixed) has projective dimension 8 and degree 2.
This means there are many (∞^8) rank-one matrices in F+L_1, but their quotient images span
at most 3 dimensions over F_3 (analysis), confirming the frozen-span obstruction extends beyond
τ-fixed generators.

### Result C: f-parity invariant

**Theorem**: Under free-free orbit flips and free-orbit reductions, f mod 2 is invariant.
Since rank = f + 2m, rank parity equals f parity.

- naive_27: f = 9 (odd), rank = 27. All reachable ranks are odd.
- Laderman(τ): f = 7 (odd), rank = 23. All reachable ranks are odd.
- Rank 22 requires f even. **Unreachable by current walk moves.**

Parity-changing moves:
1. Orbit collapse: (f,m) → (f+1, m-1), Δr = -1
2. Fixed-term addition: (f,m) → (f+1, m), Δr = +1
3. Fixed-term removal: (f,m) → (f-1, m), Δr = -1

The analysis null result (all 72 one-ARTIFACT flips stay at (9,9) rank 27) is structurally
necessary, not a search failure.

### Result D: Laderman's special L_sym structure

At the transported Laderman (7,8) witness:

1. **Free symmetric products have zero L_sym quotient**: the 8 free orbit symmetric products
   lie entirely in F. dim(F + free_sym) = dim(F) = 16.

2. **All L_sym coverage comes from the 7 fixed terms**: their L_sym projections form a
   near-basis of L_sym (terms 4,10,12,19,21,23 each contribute one independent coordinate;
   term 1 has zero L_sym projection).

3. **Despite surjective projection, direct deletion FAILS**: deleting any fixed term
   (including term 1 with zero L_sym projection) breaks L_sym containment.
   rank(remaining 22 + L_sym) = 23 for every deletion. This is because the 6 remaining
   fixed quotient images span a 6-dim space NOT aligned with L_sym in K^65.

4. **L_anti containment is robust**: every fixed deletion preserves L_anti ⊆ F.

**analysis correction to the structural interpretation**: the phrase "free symmetric quotient" is misleading. For every free orbit, not only at Laderman,
\[
 v_j\odot w_j=(v_jP(w_j)^T+w_jP(v_j)^T)/2
\]
lies in its own two-dimensional free span F_j. Thus free symmetric products have zero image modulo the full free span F identically. The real invariant is not a quotient contribution but the intersection
\[
 s(F)=\dim(F\cap L_{\mathrm{sym}}).
\]
If the anti condition gives \(L_{\mathrm{anti}}\subset F\), then
\[
 q(F)=\dim((F+L_1)/F)=6-s(F).
\]
A skeleton with f fixed terms can only work if \(q(F)\le f\), and the fixed square images must span the target quotient in \((F+L_1)/F\) (with extra fixed squares allowed outside \(F+L_1\) when \(q(F)<f\)). Laderman has \(s(F)=0\), \(q(F)=6\), and only three compatible fixed-square quotient directions, which excludes the frozen free span. A (6,8) candidate still has f=6 and need not increase s(F); it must move the eight free orbits so the fixed-square compatibility locus Z(F) supplies six independent quotient directions. For (4,9), (2,10), and (0,11), the corresponding targets require special loci with \(s(F)\ge2,4,6\), respectively.

## Corrected implication for the search

The frozen-span theorem + direct deletion failure show that the transported Laderman free span is not compressible, but the mechanism is not a generic free-symmetric quotient. The computable object is:
\[
Z(F)=\{[x]\in\mathbb P^8: xP(x)^T\in F+L_1\}
\]
when \(q(F)=f\), and its natural fixed-square quotient generalization when \(q(F)<f\). A (6,8) search should move the eight anti-feasible free planes and track the dimension/degree/finite-field population and quotient rank of Z(F). For (4,9), the target is to find anti-feasible nine-plane spans with \(s(F)\ge2\) and four fixed squares whose quotient images contain \((F+L_1)/F\).

## Files

- [two_sector_Qi_compat.py](../code/two_sector_Qi_compat.py): two-sector + Q(i) ideal generation
- [quotient_structure.py](../../quotient_cores/code/quotient_structure.py): L_sym projection analysis  
- [correct_Lsym_projection.py](../../quotient_cores/code/correct_Lsym_projection.py): corrected RREF projection
- [decisive_containment.py](../../quotient_cores/code/decisive_containment.py): direct rank containment tests
- [compatibility_Qi.sing](../code/two_sector/compatibility_Qi.sing): Singular input (Q(i), degree 3)
- [compatibility_Qi_bilinear.sing](../code/two_sector/compatibility_Qi_bilinear.sing): bilinear ideal (dim 8, deg 2)
- [two_sector_results.json](../results/two_sector/two_sector_results.json): summary data
- [decisive_containment.json](../results/two_sector/decisive_containment.json): deletion results
- [correct_Lsym_projection.json](../results/two_sector/correct_Lsym_projection.json): projection data
