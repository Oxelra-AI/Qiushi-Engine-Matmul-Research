# convention-correct Laderman transport and anti-sector correction

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

analysis concluded `m_0(L_anti)=9`, but that conclusion used two assumptions that do not hold for the transpose layer:

1. A free `tau` orbit has arbitrary vectors `v,w in K^9` (arbitrary `3 x 3` matrices). It is not restricted to row-pure vectors of the form `alpha tensor r` and `beta tensor r`.
2. The Laderman anti-sector test used the standard-`tau` bivector formula on a decomposition whose involution is `Phi_3 Phi_4`, not the standard transpose involution. The nonzero bivectors on six of seven `Phi_3 Phi_4`-fixed terms are the visible symptom of this convention mismatch.

This note records the corrected exact computation. It supersedes analysis's `m_0=9` conclusion and the skeleton eliminations derived from it.

## Transport from `Phi_3 Phi_4` to standard `tau`

Let

\[
\tau(A,B,C)=(A^T,C^T,B^T).
\]

In the analysis Burichenko convention the Laderman scheme is invariant under
`Phi = Phi_3 Phi_4`. With

\[
\pi_{12}=E_{12}+E_{21}+E_{33},\qquad
\epsilon_1=\operatorname{diag}(-1,1,1),\qquad
\epsilon_2=\operatorname{diag}(1,-1,1),
\]

put

\[
Q=\epsilon_1\pi_{12}=\pi_{12}\epsilon_2,
\qquad R=\operatorname{diag}(i,1,1),\quad i^2=-1,
\qquad P=I.
\]

Define the sandwich automorphism

\[
g(A,B,C)=\bigl(PAQ^{-1},\; QBR^{-1},\; RCP^{-1}\bigr).
\]

The scripts verify on the full matrix-unit basis that

\[
\tau\,g=g\,\Phi,
\qquad\text{equivalently}\qquad \Phi=g^{-1}\tau g,
\]

using the identities `Q = eps1*pi12 = pi12*eps2` and `R^T R = eps1`.

This displayed diagonal transport is defined over fields containing a square root of `-1`. It is implemented exactly over `Q(i)` and over `F_65521`, where `41224^2 = -1`. review correctly pointed out that this is only a convenient normalization, not the general field condition. If we replace `Q` by `delta Q` it is enough to find `R` with

\[
R^T R=\delta\epsilon_1.
\]

The script [transport_laderman_general_ff.py](../code/transport_laderman_general_ff.py) finds such scaled congruences and replays the transport over `F_3,F_5,F_7,F_11,F_13`. In all five fields it verifies `tau g = g Phi`, exact replay of `T_333`, the standard tau permutation, zero bivectors on the seven fixed terms, and eight free bivectors spanning `L_anti`. Thus the finite-field standard-tau Laderman eight-witness is available over tested odd finite fields including `F_3`; the earlier statement that `F_3` cannot use the transport was too strong. Over `Q` or `R`, the displayed diagonal normalization is impossible and the relevant quadratic-form congruence requires separate treatment.

## Exact checks

Scripts and data:

- [transport_laderman_to_standard_tau.py](../code/transport_laderman_to_standard_tau.py)
- [transported_laderman_standard_tau_F65521.json](../results/transport_laderman_tau/transported_laderman_standard_tau_F65521.json)
- [transport_laderman_qi.py](../code/transport_laderman_qi.py)
- [transported_laderman_standard_tau_Qi.json](../results/transport_laderman_tau/transported_laderman_standard_tau_Qi.json)
- seven-subset check: [laderman_m7_subsets.py](../code/laderman_m7_subsets.py), [transported_laderman_m7_subsets_F65521.json](../results/transport_laderman_tau/transported_laderman_m7_subsets_F65521.json)

Both exact replays establish:

1. The transported 23 terms still sum to `T_333` exactly.
2. The standard `tau` permutation of transported terms is the analysis `Phi_3 Phi_4` permutation: seven fixed terms and eight two-cycles.
3. All seven standard-`tau` fixed terms have zero standard bivector `v wedge w` after identifying the third factor by transpose.
4. The eight free-orbit representative bivectors have rank `8` and contain the standard complementary target `L_anti`:
   \[
   \operatorname{rank}(\eta_1,\ldots,\eta_8)=
   \operatorname{rank}(\eta_1,\ldots,\eta_8,L_{\rm anti})=8.
   \]
5. Over `Q(i)` the target rows are expressed in the eight representative bivectors by
   \[
   \begin{pmatrix}
   1&1&-1&-1&0&0&0&0\\
   0&0&1&0&1&1&1&0\\
   0&0&-1&-1&-1&0&0&1
   \end{pmatrix}.
   \]
6. In this transported Laderman witness, no seven of the eight representative bivectors contains `L_anti`; every seven-subset has defect `1`. This only proves that this particular eight-witness is internally minimal. It is not a theorem that `m_0 >= 8`.

Thus, over `C`, `Q(i)`, `F_65521`, and the tested odd finite fields `F_3,F_5,F_7,F_11,F_13`,

\[
m_0(L_{\rm anti})\le 8.
\]

Combined with the analysis A-wedge determinant lower bound, the currently proved range over these fields is

\[
7\le m_0(L_{\rm anti})\le 8.
\]

For a field where neither the diagonal `sqrt(-1)` transport nor the scaled congruence has been realized, the universal analysis range remains

\[
7\le m_0(L_{\rm anti})\le 9,
\]

unless an independent eight-bivector witness over that field is found.

## What analysis got wrong

The decomposition

\[
\Lambda^2(U\otimes C)
=\bigl(\Lambda^2U\otimes\operatorname{Sym}^2C\bigr)
\oplus
\bigl(\operatorname{Sym}^2U\otimes\Lambda^2C\bigr)
\]

is still the right framework. The error was replacing arbitrary free-orbit vectors

\[
v=\sum_i e_i\otimes r_i,
\qquad
w=\sum_i e_i\otimes s_i
\]

by row-pure vectors. In the signal direction `e_a wedge e_b`, a single arbitrary free bivector contributes

\[
r_a\odot s_b-r_b\odot s_a\in\operatorname{Sym}^2C,
\]

which can have full rank `3` as a quadratic form. Therefore one cannot count each bivector as a single square in one `Lambda^2 U` direction. The Waring-rank-three count for `q=I_3` applies only to the no-noise pure case.

A correct small lemma remains useful:

**Pure/no-noise lemma.** For a single decomposable bivector `v wedge w` in `Lambda^2(U tensor C)`, the projection to `Sym^2 U tensor Lambda^2 C` vanishes exactly when the two-plane `span(v,w)` is contained in `U tensor <r>` for some line `<r> in P(C)`. Equivalently, after changing the basis of the two-plane,

\[
v=\alpha\otimes r,
\qquad w=\beta\otimes r.
\]

Then the signal is `(alpha wedge beta) tensor r^2`. This explains why the canonical nine-bivector upper bound is square/pure, but it does not imply that every minimal or near-minimal configuration is square/pure. The transported Laderman eight-witness is precisely a noise-canceling non-pure configuration.

## Correct transpose-layer consequences

The analysis conclusion `m_0=9` is false over algebraically closed characteristic zero. Therefore the analysis eliminations of the tau skeletons `(8,7)` and `(6,8)` are withdrawn.

The currently supported transpose skeleton state is:

- `(12,5)` and `(10,6)` are still excluded by analysis's rigorous `m_0 >= 7` complementary-sector lower bound.
- `(8,7)` remains unresolved; it exists only if `m_0=7` and the coupled Gram/full-containment equations are satisfiable.
- `(6,8)` is now a natural Laderman-adjacent target: Laderman itself is `(7,8)` at rank 23, and its eight free standard-`tau` bivectors already cover the anti target after transport over `Q(i)`/`C`.
- `(4,9)`, `(2,10)`, `(0,11)` remain open.

The walk conclusion from analysis must also be repaired. Free-free flips at fixed `f=9` would reach `(9,7)` at rank 23 only if `m_0=7`; this is unresolved, not excluded. Fixed-term-touching plus-transitions remain important, but they are no longer forced by a proved `m_0=9` theorem.

## Next mathematical work

The useful exact problem is not to prove `m_0=9`, but to classify or solve the noise-canceling incidence:

\[
S:K^m\to\Lambda^2U\otimes\operatorname{Sym}^2C,
\qquad
N:K^m\to\operatorname{Sym}^2U\otimes\Lambda^2C.
\]

Containment `L_anti subset span{eta_j}` means that some three-dimensional subspace of `ker N` has `S`-image `Lambda^2U tensor <q>`. For `m=7,8` this is a small determinantal incidence and should be handled directly or through a symmetry-guided exact solver, not by random misses or by hard-coding the canonical nine.

For rank-22 transpose search, solve the coupled full containment with free pairs genuinely free and recover `u` linearly at the end. The `(6,8)` layer deserves special attention because the transported Laderman `(7,8)` positive control shows the anti half is already achievable with eight free orbits over `C`/`Q(i)`.

## Fixed-free completion tests after the transport correction

With the transported Laderman eight free orbits held fixed, let `F` be the span of their sixteen full slice rank-one matrices `vec(b) vec(c)^T`. Exact computations over `F_65521`, `F_5`, and `F_3` all give

\[
\dim F=16,
\qquad
\dim(F+L_1)=22,
\qquad
\dim((F+L_1)/F)=6.
\]

This means a rank-22 compression with the same eight free orbits and six additional generators is dimension-tight. Direct deletion of any one of Laderman's seven old fixed terms fails: each six-old-fixed subset leaves full-containment defect `1`.

### Six standard-tau fixed generators

Scripts:

- [fixed_completion_enum.py](../../occupation_and_completion/code/fixed_completion_enum.py)
- [fixed_completion_general_ff.py](../../occupation_and_completion/code/fixed_completion_general_ff.py)
- outputs [fixed_completion_enum_F5.json](../../occupation_and_completion/results/fixed_completion_enum/fixed_completion_enum_F5.json) and [fixed_completion_general_finite_fields.json](../../occupation_and_completion/results/fixed_completion_enum/fixed_completion_general_finite_fields.json)

Over `F_5`, full projective enumeration of `P^8(F_5)` found only three standard-tau fixed candidates `x(v)=vec(V)vec(V^T)^T` lying in `F+L_1`, and their quotient images have rank `3`, not `6`. Singular on the homogeneous compatibility ideal (59 quadrics) gives affine dimension `1`, projective dimension `0`, and projective degree `3`; the only nonempty unit charts are `x2=1`, `x5=1`, and `x8=1`, matching the three enumerated points. This strongly supports that the fixed-candidate variety over `\overline{F}_5` is just these three reduced points, although a formal write-up should save or reproduce the primary decomposition.

Using the general scaled-congruence transport, the same fixed-candidate enumeration over `F_3` also found only three compatible projective fixed vectors, with quotient rank `3`. Therefore no `(6,8)` standard-tau completion exists over `F_3` or `F_5` while holding the transported Laderman eight free orbits fixed and requiring the six added generators to be tau-fixed.

### Six unrestricted rank-one generators

Script:

- [general_completion_fixed_free.py](../../occupation_and_completion/code/general_completion_fixed_free.py)
- output [general_completion_fixed_free_F3.json](../../occupation_and_completion/results/general_completion/general_completion_fixed_free_F3.json)

This stronger test holds the same sixteen free slots fixed but allows the six additional generators to be arbitrary rank-one matrices `v w^T` over `F_3` (not tau-fixed). The first run stopped after one candidate because of a Python conditional-expression precedence bug; it is superseded. After patching, the complete `P^8(F_3)` scan over left vectors found only three rank-one compatible quotient directions, again of span rank `3<6`. Thus even unrestricted six rank-one completions do not exist over `F_3` with Laderman's transported free slots fixed.

This is still a fixed-free-span result. A genuine `(6,8)` tau-rank-22 scheme may move the eight free orbits; the fixed-span miss is valuable because it says the nearby compression cannot simply keep Laderman's anti-sector witness and adjust six fixed terms.

## Compact eight-bivector certificate

For later proof work, the script [extract_8bivector_certificate.py](../../finite_certification/code/extract_8bivector_certificate.py) saves a small exact certificate independent of the long transport replay:

- [laderman_8bivector_certificate_Qi.json](../results/transport_laderman_tau/laderman_8bivector_certificate_Qi.json)
- [laderman_8bivector_certificate_Qi.md](transport_laderman_tau/laderman_8bivector_certificate_Qi.md)

It records the eight free pairs, the wedge-coordinate convention, an `8 x 8` minor with determinant `-1`, and the `3 x 8` coefficient matrix expressing the three `L_anti` target rows in the eight transported Laderman bivectors. It also records that deleting any one of the eight witness bivectors leaves augmented rank `8` vs rank `7`.
