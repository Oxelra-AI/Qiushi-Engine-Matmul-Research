# Superseded by analysis repair

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

analysis found and repaired a substantive error in this note.  The sentence in §2 that uses unrestricted rank additivity for disjoint-support tensors is not a theorem: Strassen's direct-sum conjecture is false in general (Shitov 2019), and review had already warned that finite torsion layers require direct lower bounds on merged blocks.  The finite-order aligned statement in §4 item 2 must be read only as a proposed statement until replaced by [torsion_layer_repair.md](../../symmetry_and_residuals/notes/torsion_layer_repair.md).  The valid part retained from this note is the power reduction: if a finite-order symmetry permutes summands with permutation order d, then the d-th power fixes each summand projectively; applying that reduction requires a separately proved finite-order termwise theorem.

# Corrected multiplicative transfer and finite-order symmetry exclusion

## review correction and resolution

review (independent-verification-record) correctly identified that
the original "equality pattern transfer" argument was **wrong**: the 6425 additive flats
from analysis do not directly enumerate all multiplicative weight patterns.  Specifically,
for roots-of-unity eigenvalues of order $d$, the multiplicative block partition coarsens
the additive one via mod-$d$ congruences, and some coarsened patterns cannot be realized
by any additive weights (they force centrality in characteristic zero).

However, this gap has a **clean fix** via the index-disjointness lemma below.  The fix
was verified computationally for $d = 2, \ldots, 12$ at
[index_disjointness_verification.json](../results/index_disjointness/index_disjointness_verification.json).

---

## 1. Index-disjointness lemma

**Lemma.** For $d \ge 3$, suppose two distinct support triples $(a,b,c)$ and $(a',b',c')$
of $T_{\langle3,3,3\rangle}$ (with $a,b,c,a',b',c'\in\{0,1,2\}$) satisfy
$$
a - b \equiv a' - b' \pmod{d} \quad\text{and}\quad b - c \equiv b' - c' \pmod{d}
$$
but $(a-b, b-c) \neq (a'-b', b'-c')$ as integer pairs.  Then $a \neq a'$, $b \neq b'$,
and $c \neq c'$.

**Proof.** Suppose $a = a'$.  Then $a - b \equiv a - b' \pmod{d}$, hence
$b \equiv b' \pmod{d}$.  Since $b, b' \in \{0,1,2\}$ and $d \ge 3$, we get $b = b'$.
Then $b - c \equiv b - c' \pmod{d}$ gives $c = c'$ by the same argument.
But $(a,b,c) = (a',b',c')$ contradicts "distinct triples."  The same reasoning applies
if $b = b'$ or $c = c'$.  $\square$

**Computational verification.** The script `index_disjointness.py` confirms
zero violations for all $d \in \{3,4,\ldots,12\}$ and 36 violations for $d = 2$.

---

## 2. Corrected multiplicative transfer theorem

**Theorem (Finite-order aligned exclusion, characteristic zero).**
Let $K$ be a field of characteristic zero, and let
$g = \phi_{U,V,W}$ be a nontrivial De Groote element of finite order
that fixes every summand of a full-span rank-$r$ decomposition of
$T_{\langle3,3,3\rangle}$ projectively.  Then $r \ge 23$.

**Proof.** Over $\bar K$, $g$ is semisimple (finite order, char 0).  After
diagonalization, $U,V,W$ are diagonal with eigenvalues $(p_a), (q_b), (r_c)$.
Each summand corresponds to a support triple $(a,b,c)$ with multiplicative
weight $(p_a/q_b,\, q_b/r_c)$.  The decomposition splits block-by-block
according to the multiplicative weight equality.

**analysis: Identify the additive flat.**
Write $p_a = e^{2\pi i P_a/n}$ (etc.) for some integer exponents $P_a, Q_b, R_c$
with period $n$ (the order of $g$).  The **additive** weight of triple $(a,b,c)$
is $(P_a - Q_b,\, Q_b - R_c) \in \mathbb Z^2$.  Two triples with the same
additive weight automatically have the same multiplicative weight.  So the
additive block partition **refines** the multiplicative one.

Since $g$ is noncentral, the additive weight pattern is one of the 6424
noncentral flats from analysis (the arrangement analysis is over $\mathbb Q$
and applies to all integer weight vectors).  The analysis certified block-rank sum
for every noncentral flat is $\ge 23$.

**analysis: Coarsening preserves the sum.**
The multiplicative block partition is a coarsening: it merges additive blocks
whose integer differences are congruent modulo $d$ (the relevant period).
Within each multiplicative block, the additive sub-blocks contain support
triples whose integer weights differ.

By the index-disjointness lemma (for $d \ge 3$ of the eigenvalue ratios):
any two triples in the same multiplicative block but different additive sub-blocks
share **no** coordinate index.  Therefore the sub-tensors on different additive
sub-blocks have **disjoint support**, and for disjoint-support tensors, rank is
additive:
$$
R\Bigl(\bigoplus_i T_i\Bigr) = \sum_i R(T_i).
$$

Hence
$$
R(\text{multiplicative block}) = \sum_{\text{additive sub-blocks}} R(\text{sub-block})
\ge \sum_{\text{additive sub-blocks}} (\text{certified lower bound}).
$$

Summing over all multiplicative blocks gives the same total as summing over
all additive blocks, which is $\ge 23$ by analysis.  $\square$

**analysis: The $d \le 2$ case.**
For $d = 1$ (identity permutation), the multiplicative weight *is* the additive
weight (no coarsening), and analysis applies directly.

For $d = 2$: the index-disjointness fails, but for a **sandwich** element
$\phi_{F,F,F}$ with three distinct eigenvalues, $d = 2$ is impossible
(since $F^2 = sI$ forces at most two distinct eigenvalues).  For a general
De Groote element with $d = 2$, a separate analysis of the block structure
is required; this is recorded as an open case.

---

## 3. The $g^d$ reduction (unchanged)

**Corollary.** If a nontrivial finite-order De Groote element $g$ permutes
the summands of a rank-22 decomposition with nontrivial permutation $\pi$
of order $d$, then $g^d$ fixes every summand projectively.  If $g^d$ is
noncentral, the theorem above gives $r \ge 23$, contradiction.  So $g^d$
must be central.

---

## 4. Summary: what is proved, what is open

### Proved (characteristic zero):

1. **Aligned exclusion for Lie-algebra elements** (earlier analysis):
   No full-span rank-22 decomposition admits a noncentral Lie-algebra stabilizer
   element acting projectively termwise.

2. **Aligned exclusion for finite-order elements** (this ARTIFACT):
   No full-span rank-22 decomposition admits a noncentral finite-order De Groote
   element acting projectively termwise.  Proof uses earlier analysis plus the
   index-disjointness lemma (valid for $d \ge 3$) and the $d = 2$ impossibility
   for sandwich with 3 distinct eigenvalues.

3. **$g^d$ reduction**: Any finite-order symmetry either fixes every summand
   (excluded above) or has $g^d$ central.

### Open:

- **Orbit-permuting symmetry** ($g^d$ central): The orbit structure for each
  skeleton $(d, m, f)$ needs algebraic analysis beyond eigenspace dimensions.
  Over $\mathbb F_2$, the order-7 family is excluded (analysis certificate);
  the order-3 budget argument is insufficient (orbit sums span $L_0$, analysis).

- **$d = 2$ non-sandwich De Groote elements**: Requires separate block-rank
  analysis for the $d = 2$ coarsening.

- **Transverse decompositions**: No symmetry at all.

- **Positive characteristic**: The CHL inputs are char-0 only.

---

## 5. Relation to prior work

The aligned exclusion for finite-order elements is a genuine extension of earlier analysis.
The published literature (Yang 2024, BILR) searches symmetric decompositions
computationally but does not contain a block-rank argument.  The closest prior result
is the Lie-algebra version from earlier analysis; the extension to finite-order elements
via the index-disjointness lemma is new.

The combined result says: over characteristic zero, any rank-22 algorithm for
$3\times3$ matrix multiplication must be "transverse" (no nontrivial aligned
stabilizer), and any symmetry it possesses must act as a genuine permutation
with central power.  This rules out the mechanism by which all known rank-23
algorithms are invariant (termwise projective scaling).

## 6. Files

- [multiplicative_transfer_and_symmetry.md](../../symmetry_and_residuals/notes/multiplicative_transfer_and_symmetry.md): superseded by this note
- [index_disjointness.py](../code/index_disjointness.py): verification of the index-disjointness lemma
- `workspace/data/index_disjointness/`: verification results
- [order3_certificate.py](../../symmetry_and_residuals/code/order3_certificate.py): order-3 F₂ budget analysis
- `workspace/data/order3_certificate/`: order-3 F₂ results (budget insufficient)
- `independent-verification-record`: review correction that led to the fix
