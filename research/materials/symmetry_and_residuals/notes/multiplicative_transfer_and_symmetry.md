# Superseded by analysis repair

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This first analysis draft used an invalid equality-pattern/direct-sum transfer.  General tensor-rank additivity for direct sums is false, and finite-order torsion layers are not covered by the Lie-algebra arrangement through Zariski closure.  Use [torsion_layer_repair.md](torsion_layer_repair.md) instead.  The only retained part is the elementary power reduction for orbit-permuting symmetries: a symmetry whose induced summand permutation has order d has a d-th power that fixes each summand projectively.

# Multiplicative weight transfer and extended symmetry exclusion

## 1. The multiplicative transfer lemma

### Context

earlier analysis proved that over characteristic zero, no full-span rank-22 decomposition
of $T_{\langle3,3,3\rangle}$ admits a noncentral **Lie-algebra** stabilizer element acting
projectively termwise. The proof uses three ingredients:

- (A) Nonsemisimple alignment forces semisimplicity (analysis lemma)
- (B) Semisimple elements decompose the 27 support triples into weight blocks
- (C) Block-rank sums from $M_{\langle3,3,2\rangle}\ge14$ etc. give sum $\ge23$ for all 6424 noncentral flats

That argument uses **additive** weights $(p_a - q_b,\, q_b - r_c)$ for a Lie-algebra
element $(P,Q,R)$ with eigenvalues $p_0,p_1,p_2$ on factor $A$, etc.

### Statement

**Lemma (Multiplicative weight transfer).** The block-rank exclusion of analysis
applies identically to any **finite-order** De Groote element
$\phi_{U,V,W}$ acting projectively on every summand (termwise aligned).

### Proof

Let $g = \phi_{U,V,W}$ be a finite-order element of the stabilizer $\operatorname{Stab}(T_{333})$,
acting on a full-span rank-$r$ decomposition by scaling each summand
$u_i\otimes v_i\otimes w_i$ by a multiplicative eigenvalue.  Assume $K$ is algebraically
closed of characteristic zero; then $g$ is semisimple (being of finite order)
and diagonalizable.

After conjugation, $U = \operatorname{diag}(p_0,p_1,p_2)$, $V = \operatorname{diag}(q_0,q_1,q_2)$,
$R = \operatorname{diag}(r_0,r_1,r_2)$.  Since $g$ acts termwise, each summand is a weight
vector; the action on the $(a,b)$-entry of the $A$-factor is
$A_{ab} \mapsto (p_a/q_b)\, A_{ab}$, on the $B$-factor $(q_c/r_d)\, B_{cd}$,
on the $C$-factor $(r_e/p_f)\, C_{ef}$.

Each summand corresponds to one of the 27 support triples $(a,b,c)$ of $T_{333}$
(where $A=e_{ab}, B=e_{bc}, C=e_{ca}$) with **multiplicative** weight vector
$$
w(a,b,c) = \bigl(p_a/q_b,\, q_b/r_c\bigr) \in (K^*)^2.
$$

Two triples $(a,b,c)$ and $(a',b',c')$ lie in the **same weight block** iff
$$
p_a/q_b = p_{a'}/q_{b'} \quad\text{and}\quad q_b/r_c = q_{b'}/r_{c'}.
$$

These equalities are equivalent to
$$
p_a/p_{a'} = q_b/q_{b'} = r_c/r_{c'}.
$$

This is exactly the same **equality pattern** as the additive condition
$p_a - p_{a'} = q_b - q_{b'} = r_c - r_{c'}$ from the Lie-algebra case.
Specifically, the block partition depends only on:

1. Which pairs $(i,j)$ have $p_i = p_j$ (equivalence classes of $A$-eigenvalues)
2. Which pairs $(i,j)$ have $q_i = q_j$ ($B$-eigenvalues)
3. Which pairs $(i,j)$ have $r_i = r_j$ ($C$-eigenvalues)
4. Which cross-factor equalities $p_a/p_{a'} = q_b/q_{b'}$ hold

Over an algebraically closed field of characteristic zero, both the additive
group $(K,+)$ and the multiplicative group $(K^*,\times)$ are divisible, and the
set of **realizable equality patterns** is the same for both (any combination
of equalities/inequalities among three values can be realized in either group).

Therefore the 6425 flats enumerated in analysis exhaust all possible block partitions
for both additive and multiplicative weights.  The block-rank lower bounds are
purely combinatorial (depending only on the block structure, not on the specific
weight values), so the certified sums $\{23:36,\, 24:108,\, 25:27,\, 27:6253\}$
apply to every noncentral multiplicative weight pattern.

**Conclusion:** For $r=22$, every noncentral weight pattern gives block-rank
sum $\ge 23$, contradicting $r=22$.  Hence no noncentral finite-order De Groote
element can act projectively on every summand of a full-span rank-22 decomposition
of $T_{333}$ over any algebraically closed field of characteristic zero.  $\square$

### Remark on sandwich specialization

For a **sandwich** element $\phi_{F,F,F}$, we have $U=V=W=F$, so
$p_i = q_i = r_i$ for all $i$.  The weight becomes
$(p_a/p_b,\, p_b/p_c)$, which is a special case of the general De Groote
weight.  The same exclusion applies a fortiori.

### Remark on field extension

The result holds over any field $K$ of characteristic zero by embedding
$K \hookrightarrow \bar K$ (algebraic closure).  A rank-$r$ decomposition
over $K$ remains rank-$r$ over $\bar K$, and a nontrivial stabilizer element
remains nontrivial.

---

## 2. Extension to orbit-permuting symmetries: the $g^d$ reduction

### Statement

**Proposition.** Let $K$ be a field of characteristic zero, and let
$g\in\operatorname{Stab}(T_{333})$ be a nontrivial element of finite order $n$.
Suppose $T_{333} = \sum_{i=1}^{22} x_i$ (rank-one summands) and $g$ permutes
$\{x_1,\ldots,x_{22}\}$ with induced permutation $\pi$ of order $d\,|\,n$.

Then $g^d$ fixes every summand projectively.  If $g^d$ is noncentral,
the multiplicative transfer lemma excludes the decomposition.
If $g^d$ is central (scalar on each tensor factor), then $g$ acts as a
genuine permutation of order $d$ on the 22 summands, with orbit sizes
summing to 22 and each orbit size dividing $d$.

### Proof

Since $\pi^d = \operatorname{id}$, we have $g^d(x_i) \propto x_i$ for all $i$.
Over characteristic zero, $g^d$ is semisimple, so diagonalizable.

If $g^d$ is noncentral: the Zariski closure of $\langle g^d\rangle$ in
$\operatorname{GL}(E)$ is a torus $T$, and $\operatorname{Lie}(T)$ contains
a noncentral element $h$ with the same eigenspaces as $g^d$.  Since $g^d$
fixes every summand projectively, so does $h$.  The multiplicative transfer
lemma (or equivalently the original Lie-algebra theorem) then applies to $h$
and gives a contradiction.

If $g^d$ is central: then $g^d = \lambda\cdot\operatorname{id}$ for some scalar
$\lambda$, and $g$ acts on $\{x_i\}$ by a permutation of order exactly $d$
composed with eigenvalue scalings that are $d$-th roots of unity times a
common factor.  $\square$

### Consequence for sandwich symmetries

For a diagonal sandwich element $g=\phi_{F,F,F}$ of order $n$ with
$F=\operatorname{diag}(p_0,p_1,p_2)$:

- $g^d$ central means $p_i^d = s$ for all $i$ (common scalar), so
  the eigenvalue ratios $p_i/p_j$ are $d$-th roots of unity.
- For $d=1$: $g$ fixes every summand (aligned case), excluded by Sec. 1.
- For $d=2$: would need three distinct values among $\{p_0,p_1,p_2\}$
  with all ratios being $\pm1$, which is impossible (only two values
  available in $\{\pm1\}$).
- For $d\ge3$: the orbit structure is $f + \sum d_i = 22$ with $d_i\mid d$,
  $d_i\ge2$, and each $d_i$-orbit consists of rank-one summands cyclically
  permuted by $g$.

---

## 3. The orbit-permuting case: eigenspace budget (characteristic zero)

For a sandwich element $g$ of order $d\ge3$ with $g^d$ central, the
$\sigma$-projector $\sigma = \frac{1}{d}\sum_{k=0}^{d-1} g^k$ maps $S$
(the 22-dim UV span) to $\sigma(S) = S\cap \operatorname{Fix}(E)$, which
has dimension at most $f + m$ (where $f$ = fixed summands, $m$ = free orbits).

**The constraint** $L_0 = L\cap\operatorname{Fix}(E) \subseteq \sigma(S)$
must hold.

### Characteristic-zero eigenspace dimensions

For a sandwich with three distinct eigenvalues whose ratios are
primitive $d$-th roots of unity:

- **Generic** (multiplicatively independent ratios, or $d\ge5$ with
  eigenvalues $\zeta^{a_0},\zeta^{a_1},\zeta^{a_2}$ for distinct $a_i$):
  $\dim\operatorname{Fix}_{\mathbb C}(E) = 15$.

- **Order 3** ($d=3$, eigenvalues $1,\omega,\omega^2$):
  The fixed condition on $(a,b,c,d)\in\{0,1,2\}^4$ is
  $a-b+c-d\equiv0\pmod3$, giving $\dim\operatorname{Fix}(E) = 27$.

- **Order $d\ge5$** (with $\max|a_i-a_j|\le2$ and $d>4$):
  $a-b+c-d\equiv0\pmod d$ with $|a-b+c-d|\le4 < d$ forces
  $a-b+c-d=0$, giving $\dim\operatorname{Fix}(E) = 15$.

In all cases, $\dim L_0 = 3$ (since Fix$(h_W)$ = diagonal matrices, dim 3,
and $T_{\mathrm{flat}}$ is injective on Fix$(h_W)$).

### Saturated dimension count

For skeleton $(m,f)$ with $f+dm = 22$:

Each free $d$-orbit contributes 1 dim to each of $d$ eigenspaces of $g$.
Fixed summands contribute only to $\operatorname{Fix}(E)$.

Total: $\dim S = f + dm = 22$ (saturated).

Eigenspace decomposition of $L$ (dim 9): $L_0$ (dim 3 in Fix) plus
$L_j$ (dim 1 in each of the $d-1$ non-fixed eigenspaces, for sandwich
with three distinct factor eigenvalues).

For $d\ge5$ (dim Fix(E) = 15):
- $\operatorname{Fix}(E)$: need $\dim\sigma(S)\ge 3$, have $\dim\sigma(S)=f+m$.
- Each non-fixed eigenspace $E_j$ (dim 11): need $\dim S_j\ge1$, have $\dim S_j=m$.
  So $m\ge1$.
- Total: $f+dm = 22$, $m\ge1$, $f+m\ge3$.

For $d=7$: $22=7m+f$, so $(m,f)\in\{(3,1),(2,8),(1,15),(0,22)\}$.
  - $(0,22)$: aligned case, excluded.
  - $(1,15)$: $f+m=16\ge3$ ✓, $m=1\ge1$ ✓, but $f=15$ means 15 fixed rank-one
    points must be chosen. Over $\mathbb C$, there are continuously many fixed
    rank-one points (the Segre variety in $\operatorname{Fix}(E)$), so this is
    not ruled out by dimension alone.
  - $(2,8)$: $m=2$, each non-fixed $E_j$ gets 2 dims. $\dim L_j=1\le2$ ✓.
  - $(3,1)$: saturated, $\dim S=22$ exactly.

The eigenspace dimensions alone do **not** exclude the orbit-permuting case
for $d\ge5$ over $\mathbb C$.  The exclusion requires the actual rank-one
conditions on the orbit representatives (each orbit element must be rank-one
in $E=K^9\otimes K^9$), which imposes stronger algebraic constraints.

### Status of characteristic-zero orbit-permuting exclusion

The aligned stratum (including finite-order elements via the multiplicative
transfer) is now **unconditionally excluded** in characteristic zero.

The orbit-permuting stratum requires either:
(a) An algebraic geometry argument showing the rank-one orbit conditions
    are inconsistent with $L\subset S$ for each skeleton, or
(b) A case-by-case computational check (finite for each $d$, but the
    algebraic system over $\mathbb C$ has continuous families of candidates).

This is the natural next frontier for the characteristic-zero lower bound.

---

## 4. Unified statement

**Theorem (Extended aligned exclusion, characteristic zero).**
Let $K$ be a field of characteristic zero.  Suppose
$$
T_{\langle3,3,3\rangle} = \sum_{i=1}^{r} u_i\otimes v_i\otimes w_i
$$
is a full-span rank-$r$ decomposition, and $g\in\operatorname{Stab}(T_{333})$
is a nontrivial De Groote element of finite order that fixes every summand
projectively ($g(u_i\otimes v_i\otimes w_i)\propto u_i\otimes v_i\otimes w_i$
for all $i$).  Then $r\ge 23$.

**Proof.** Over $\bar K$, $g$ is semisimple and diagonalizable.  After
diagonalization, the weight of each summand on the 27 support triples
is a multiplicative vector $(p_a/q_b,\, q_b/r_c)$.  The weight equality
pattern is one of the 6425 flats from the analysis arrangement.  Since
$g$ is noncentral and fixes every summand, all 27 triples contribute
to the decomposition, and the block-rank sum is at least 23 by the
certified table.  Hence $r\ge23$.  $\square$

**Corollary.** If a nontrivial finite-order De Groote element $g$ preserves
a rank-22 decomposition and permutes the summands with nontrivial permutation
$\pi$ of order $d$, then $g^d$ must be central (scalar on each tensor factor).

**Proof.** If $g^d$ is noncentral, it fixes every summand projectively,
and the theorem gives $r\ge23$, contradiction.  $\square$

---

## 5. Key inputs and their provenance

| Input | Value | Source | Field validity |
|-------|-------|--------|----------------|
| $R(M_{\langle3,3,2\rangle})\ge14$ | 14 | CHL (Forum Math Pi 2023): $\underline R(M_{\langle2,3,3\rangle})=14$ + cyclic equiv | char 0 |
| $R(M_{\langle3,2,2\rangle})\ge10$ | 10 | CHL improves to $\ge10$; Bläser gives $\ge8$ | char 0 |
| $R(M_{\langle2,2,2\rangle})\ge6$ | 6 | Exterior flattening (internally verified) | all fields |
| Arrangement enum | 6425 flats | analysis exact computation | combinatorial |
| Block-rank sums | $\ge23$ for all 6424 noncentral | analysis certified | follows from inputs |

---

## 6. What remains open

1. **Orbit-permuting sandwich symmetry over char 0**: The corollary reduces
   this to $g^d$ central, but the eigenspace budget alone does not exclude
   it for $d\ge3$.  Need: algebraic rank-one orbit analysis per skeleton.

2. **Non-sandwich De Groote symmetries**: The cycle $\Delta(A,B,C)=(B,C,A)$
   and transpose $\tau(A,B,C)=(C^T,B^T,A^T)$ are not sandwich elements.
   They permute the three tensor factors and require separate analysis.

3. **Transverse decompositions**: Decompositions with no stabilizer symmetry
   at all. This is the deepest open stratum.

4. **Positive characteristic**: The CHL input is valid only in char 0.
   The $\mathbb F_2$ order-7 certificate (analysis) uses a different method.

## 7. Files

- This note: [multiplicative_transfer_and_symmetry.md](multiplicative_transfer_and_symmetry.md)
- analysis arrangement: `workspace/data/semisimple_arrangement/`
- analysis integrated exclusion: [blaser_bound_and_nontransverse_exclusion.md](../../deformation_and_incidence/notes/blaser_bound_and_nontransverse_exclusion.md)
- CHL source: `Knowledge/objects/papers/New-lower-bounds-for-matrix-multiplication-and--64a800eb2fe7--148396182a4c/object.md`
- analysis order-7 certificate: [order7_family_certificate_v2.json](../results/order7_exhaustive/order7_family_certificate_v2.json)
