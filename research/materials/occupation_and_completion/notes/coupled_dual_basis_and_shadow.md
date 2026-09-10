# Coupled dual-basis system and 3×3 shadow reduction

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record. Field: F₂. Object: exact rank of T_{<3,3,3>} and E11 quotient core.

## 1. Transpose correction in core construction

analysis's core tensor had the B⊗C blocks at positions (i,j) corresponding to A-entry (i,j).
The correct convention (confirmed by analysis of research_record and by cn122 positive control):

  M_λ = Λ^T ⊗ I₃  (NOT Λ ⊗ I₃)

This means A-entry (i,j) maps to B⊗C block (j,i) — transposed. The correction does not
change the abstract structure (8 disjoint I₃ blocks, one missing) but changes which 
A-direction maps to which block, and critically affects the trace equations.

**Verification**: cn122 21-term core with 5 tight rank-9 contractions passes all 45 diagonal 
and all 360 off-diagonal dual-basis conditions under the corrected convention.

## 2. Dual-basis theorem and trace conditions

For a tight rank-9 contraction λ (|I_λ| = 9, rank(Λ) = 3), the active B/C factors
satisfy C^T M_λ^{-1} B = I₉.

This gives:
- Diagonal: tr(M_λ^{-1} X_t) = 1 for each active term t ∈ I_λ
- Off-diagonal: c_s^T M_λ^{-1} b_t = 0 for s ≠ t in I_λ

The diagonal condition is **linear** in the relaxed matrix variable X_t = b_t c_t^T.
It does not require rank-one X_t. So inconsistency of the linear system means no 
valid assignment of 9×9 matrices exists, regardless of rank-one.

## 3. Multi-contraction coupling: L15 analysis

For the L15 near-miss support:
- 16 tight rank-9 contractions (0 tight rank-6, 0 tight rank-3)
- Tensor-only system: consistent (rank 648)
- Full tensor + trace system: **inconsistent** (rank 736/737 in 1539-var system)
- All 16 individual contractions are consistent alone
- Minimum inconsistent subset: **exactly 8 contractions** (verified exhaustively for sizes 2-7)
- Only **2 out of 12870** 8-subsets are inconsistent

The inconsistency arises from multi-contraction coupling: shared terms must satisfy
trace conditions from multiple contractions simultaneously, and the resulting affine
constraints are incompatible with the tensor reconstruction equations.

## 4. 3×3 shadow reduction (key theoretical advance)

Define π(X)_{ij} = tr(X_{ij}) (block traces of 9×9 → 3×3). Since M_λ = Λ^T ⊗ I₃:

  tr(M_λ^{-1} X_t) = Σ_{j,i} (Λ^{-1})_{ji} · tr(X_t block(j,i)) = Σ_{j,i} (Λ^{-1})_{ji} Y_t[j,i]

where Y_t = π(X_t) ∈ Mat₃(F₂). The trace condition becomes a linear equation on
the 9 entries of Y_t.

**Equivalence theorem**: The shadow system (19 × 9 = 171 variables) is equivalent to the 
full system (19 × 81 = 1539 variables) for consistency.

Proof: If the shadow is inconsistent, the full system is also inconsistent (any X_t 
solving the full system projects to a Y_t solving the shadow). Conversely, if Y_t 
solves the shadow, any X_t with π(X_t) = Y_t can be corrected: the error in 
T_core - Σ a_t ⊗ X_t lies in A ⊗ ker(π), and since {a_t} spans F₂^8, the correction 
can be distributed among the terms' ker(π) components without affecting the trace conditions 
(which depend only on π(X_t)).

**Computational verification**: The shadow system reproduces all results from the full system:
- Tensor-only: consistent (rank 72/72)
- Full shadow: inconsistent (rank 160/161, 216 equations, 171 variables)
- All 16 individually consistent
- No inconsistent subset of size ≤ 7
- First inconsistent subsets at size 8: exactly 2 out of 12870
- Example: [42, 43, 49, 87, 94, 157, 214, 234]

The shadow system runs ~100x faster than the full system, enabling exhaustive search.

## 5. Inverse mask structure

The 16 inverse masks h_λ (9-bit coefficient vectors from Λ^{-1}) have rank 8 
(of maximum 9). This means the 16 contractions' trace conditions span an 8-dimensional
subspace of Mat₃(F₂)* — almost the full dual space.

The "missing direction" is the 1-dimensional complement of this span. The trace system
cannot distinguish Y_t values that differ along this missing direction.

## 6. Relationship to Wang occupation

The pairwise overlap bound (|I₁ ∩ I₂| ≤ ⌊(18 - rank(M₁⁻¹ + M₂⁻¹))/2⌋) is 
**exactly equivalent** to the existing Wang contraction bound w(λ₁+λ₂) ≥ rank(M_{λ₁+λ₂}).
This was proven in analysis (research_record).

However, the multi-contraction trace coupling can encode constraints **beyond** Wang:
- Wang constrains active-set sizes (|I_λ| ≥ contraction rank)
- The trace system constrains the actual factor geometry through inverse masks
- Two layers of coupling: (a) intra-term inverse-mask dependencies (odd linear dependency
  among masks touching the same term → immediate 0=1), (b) global affine reconstruction 
  (all Y_t must simultaneously satisfy trace constraints AND reconstruct the target tensor)

**Open question**: Can the trace system reject a Wang-admissible support? The L15 support 
already violates Wang (12 rows at L=12), so the trace obstruction is redundant there.
No Wang-admissible support has been found to test this. The theoretical mechanism for 
independence exists (trace equations use Λ^{-1} directions that Wang does not directly 
track), but no concrete separation has been established.

## 7. Connection to peer work, with analysis correction

research_record reports:
- Lift calibration: all 2^21 assignments on 3 rank-21 cores give rank(M₀+Δ) ≥ 3
- Core-only SAT encoding: 494 base variables, 648 equations

**analysis correction.** The core-rank bridge gives implications, not converses: ρ ≤ 19 implies R(T) ≤ 22 by adding the deleted rank-3 slice; subject to the verified full-rank-20 reduction, ρ ≥ 20 implies R(T) ≥ 21. The converses need not hold: full ranks 21 or 22 can coexist with ρ ≥ 20, and a full rank ≤22 algorithm might arise without a 19-term E11 core. Solving the nineteen-term E11-core problem would still achieve one of the research objectives, but it is not a classification of the full tensor rank.

The 3×3 shadow system can reject fixed A-supports through guarded necessary-condition cuts: the trace rows exist only for saturated rank-9 contractions of that support. It should not be treated as an unconditional XOR layer or as symmetry breaking while the A-support varies.

## 8. Files

Scripts:
- [coupled_dual_basis_system.py](../code/coupled_dual_basis_system.py): full 81-var system (corrected M_λ = Λ^T ⊗ I₃)
- [shadow_system_analysis.py](../code/shadow_system_analysis.py): compressed 9-var shadow system
- [verify_corrected_convention.py](../../quotient_cores/code/verify_corrected_convention.py): cn122 dual-basis validation
- [verify_contraction_equation.py](../code/verify_contraction_equation.py): contraction equation check

Data:
- [shadow_system_analysis.json](../results/coupled_dual_basis/shadow_system_analysis.json): complete shadow results
- [l15_corrected_trace_analysis.json](../results/coupled_dual_basis/l15_corrected_trace_analysis.json): full system results

## 9. Research state

The corrected dual-basis/trace mechanism is mathematically sound and computationally verified.
The 3×3 shadow reduction makes it tractable. The minimum inconsistent subset for L15 is 
exactly 8 out of 16 tight rank-9 contractions.

For progress toward the main goal (rank-22 or rank-≥21):
- Upper bound: the trace system gives a fast necessary condition for A-supports.
  Combined with complete Wang admissibility, it could accelerate the search for a rank-19 core.
- Lower bound: if trace coupling can independently reject Wang-admissible supports,
  it would be a genuinely new obstruction mechanism. But this is unproven.
- The peer's core SAT encoding is a direct route for the E11-core question. The shadow trace mechanism should be integrated as guarded support-dependent necessary conditions or exact fixed-support rejection before full B/C solving, not as unconditional symmetry breaking.
