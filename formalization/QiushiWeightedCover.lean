import Mathlib
import QiushiOccupationAPI
import QiushiTotalWeight
import QiushiMonotonicity

/-!
# Weighted-cover occupation certificates with the zero quotient fiber included

This module formalizes a strengthened direct-certificate observation:
a single weighted-cover certificate at target `T` can exclude every
quotient decomposition of length `r ≤ T`, without first proving the successive
same-subspace bounds `T0, T0+1, ...`.

The key point is that the zero quotient label is covered by every source
subspace `U_i ⊇ W`.  Thus the same weighted coverage inequality applies to all
terms, including those killed in the quotient by `W`.
-/

set_option maxHeartbeats 8000000
open BigOperators Finset
namespace QiushiMatmul

/-- Pure finite weighted-cover contradiction.

`kill i` is the set of decomposition indices whose A-factor lies in the source
subspace for row `i`.  If every term is covered by total row multiplier at least
`lambda0`, and each row satisfies the source lower-bound inequality
`|kill_i| + L_i ≤ r`, then a certificate
`(Σλ_i - λ0) * target < Σ λ_i L_i` contradicts any length `r ≤ target`.
This is the non-truncated arithmetic form of the usual
`Σ λ_i (target - L_i) < λ0 target` check. -/
theorem weighted_cover_infeasible_from_term_coverage
    {m r : ℕ}
    (kill : Fin m → Finset (Fin r))
    (sourceLb : Fin m → ℕ)
    (lambda : Fin m → ℕ)
    (lambda0 target : ℕ)
    (hLambda : lambda0 ≤ ∑ i : Fin m, lambda i)
    (hCoverage : ∀ t : Fin r, lambda0 ≤ ∑ i : Fin m, if t ∈ kill i then lambda i else 0)
    (hRowsAdd : ∀ i : Fin m, (kill i).card + sourceLb i ≤ r)
    (hrt : r ≤ target)
    (hCert : ((∑ i : Fin m, lambda i) - lambda0) * target <
        ∑ i : Fin m, lambda i * sourceLb i) :
    False := by
  let Λ : ℕ := ∑ i : Fin m, lambda i
  let C : ℕ := ∑ i : Fin m, lambda i * sourceLb i
  let K : ℕ := ∑ i : Fin m, lambda i * (kill i).card
  have hLower : lambda0 * r ≤ K := by
    calc
      lambda0 * r = ∑ t : Fin r, lambda0 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ t : Fin r, ∑ i : Fin m, if t ∈ kill i then lambda i else 0 := by
        exact Finset.sum_le_sum (fun t _ => hCoverage t)
      _ = K := by
        unfold K
        calc
          (∑ t : Fin r, ∑ i : Fin m, if t ∈ kill i then lambda i else 0)
              = ∑ i : Fin m, ∑ t : Fin r, if t ∈ kill i then lambda i else 0 := by
                rw [Finset.sum_comm]
          _ = ∑ i : Fin m, lambda i * (kill i).card := by
                apply Finset.sum_congr rfl
                intro i _
                calc
                  (∑ t : Fin r, if t ∈ kill i then lambda i else 0)
                      = Finset.sum (kill i) (fun _ => lambda i) := by
                        rw [← Finset.sum_filter]
                        simp
                  _ = lambda i * (kill i).card := by
                        simp [Nat.mul_comm]
  have hUpper : K + C ≤ Λ * r := by
    calc
      K + C = ∑ i : Fin m, (lambda i * (kill i).card + lambda i * sourceLb i) := by
        unfold K C
        rw [← Finset.sum_add_distrib]
      _ = ∑ i : Fin m, lambda i * ((kill i).card + sourceLb i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i : Fin m, lambda i * r := by
        exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (lambda i) (hRowsAdd i))
      _ = Λ * r := by
        unfold Λ
        rw [Finset.sum_mul]
  have hLC : lambda0 * r + C ≤ Λ * r := by
    exact le_trans (Nat.add_le_add_right hLower C) hUpper
  have hC_le_r : C ≤ (Λ - lambda0) * r := by
    have hLC' : C + lambda0 * r ≤ Λ * r := by
      simpa [Nat.add_comm] using hLC
    have hsub : C ≤ Λ * r - lambda0 * r := Nat.le_sub_of_add_le hLC'
    simpa [Nat.sub_mul] using hsub
  have hC_le_target : C ≤ (Λ - lambda0) * target :=
    le_trans hC_le_r (Nat.mul_le_mul_left (Λ - lambda0) hrt)
  have hCert' : (Λ - lambda0) * target < C := by
    simpa [Λ, C] using hCert
  exact (not_lt_of_ge hC_le_target) hCert'

/-- Derive term-level weighted coverage from a quotient label classifier.
The label set is `Fin (n+1)`: label `0` is the zero/W-coset and `Fin.succ p`
are the `n` nonzero quotient labels. -/
theorem term_coverage_from_label_cover
    {n m r : ℕ}
    (label : Fin r → Fin (n + 1))
    (mask : Fin m → Finset (Fin n))
    (kill : Fin m → Finset (Fin r))
    (lambda : Fin m → ℕ) (lambda0 : ℕ)
    (hZeroCoverage : lambda0 ≤ ∑ i : Fin m, lambda i)
    (hNonzeroCoverage : ∀ p : Fin n,
      lambda0 ≤ ∑ i : Fin m, if p ∈ mask i then lambda i else 0)
    (hZeroInKill : ∀ t : Fin r, label t = 0 → ∀ i : Fin m, t ∈ kill i)
    (hSuccInKill : ∀ (t : Fin r) (p : Fin n), label t = Fin.succ p →
      ∀ i : Fin m, p ∈ mask i → t ∈ kill i) :
    ∀ t : Fin r, lambda0 ≤ ∑ i : Fin m, if t ∈ kill i then lambda i else 0 := by
  intro t
  by_cases hzval : (label t).val = 0
  · have hz : label t = 0 := Fin.ext hzval
    calc
      lambda0 ≤ ∑ i : Fin m, lambda i := hZeroCoverage
      _ = ∑ i : Fin m, if t ∈ kill i then lambda i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [hZeroInKill t hz i]
  · let p : Fin n := ⟨(label t).val - 1, by
      have hlt : (label t).val < n + 1 := (label t).isLt
      omega⟩
    have hpval : (Fin.succ p).val = (label t).val := by
      simp [p]
      omega
    have hsucc : label t = Fin.succ p := Fin.ext hpval.symm
    have hle : (∑ i : Fin m, if p ∈ mask i then lambda i else 0) ≤
        ∑ i : Fin m, if t ∈ kill i then lambda i else 0 := by
      exact Finset.sum_le_sum (fun i _ => by
        by_cases hpm : p ∈ mask i
        · have htk : t ∈ kill i := hSuccInKill t p hsucc i hpm
          simp [hpm, htk]
        · by_cases htk : t ∈ kill i <;> simp [hpm, htk])
    exact le_trans (hNonzeroCoverage p) hle

/-- Matrix-quotient semantic weighted-cover theorem.

For a quotient decomposition modulo `W`, each source row is a superspace `U i`.
The assumptions `label_zero_mem`, `label_eq_sect_coset`, and `sect_mem_source`
connect the finite masks to actual A-cosets; source quotient-rank lower bounds
supply the row inequalities.  A weighted-cover certificate at `target` then
excludes every length `r ≤ target` decomposition. -/
theorem weighted_cover_quotient_decomp_false
    {n m r : ℕ}
    {W : Submodule F2 Mat3}
    (label : Mat3 → Fin (n + 1))
    (sect : Fin n → Mat3)
    (sourceU : Fin m → Submodule F2 Mat3)
    (sourceLb : Fin m → ℕ)
    (mask : Fin m → Finset (Fin n))
    (lambda : Fin m → ℕ) (lambda0 target : ℕ)
    (hWU : ∀ i : Fin m, W ≤ sourceU i)
    (hSource : ∀ i : Fin m, QuotientRankAtLeast (sourceU i) (sourceLb i))
    (hLabelZero : ∀ M : Mat3, label M = 0 → M ∈ W)
    (hLabelSectCoset : ∀ (M : Mat3) (p : Fin n), label M = Fin.succ p → M + sect p ∈ W)
    (hSectSource : ∀ (i : Fin m) (p : Fin n), p ∈ mask i → sect p ∈ sourceU i)
    (hZeroCoverage : lambda0 ≤ ∑ i : Fin m, lambda i)
    (hNonzeroCoverage : ∀ p : Fin n,
      lambda0 ≤ ∑ i : Fin m, if p ∈ mask i then lambda i else 0)
    (hrt : r ≤ target)
    (hCert : ((∑ i : Fin m, lambda i) - lambda0) * target <
        ∑ i : Fin m, lambda i * sourceLb i)
    (D : QuotientTensorDecomp W r) :
    False := by
  by_cases hAllLe : ∀ i : Fin m, sourceLb i ≤ r
  · let kill : Fin m → Finset (Fin r) := fun i => killSet D (sourceU i)
    have hRowsAdd : ∀ i : Fin m, (kill i).card + sourceLb i ≤ r := by
      intro i
      have hk : (killSet D (sourceU i)).card ≤ r - sourceLb i :=
        occupation_inequality (hWU i) D (hSource i) (hAllLe i)
      change (killSet D (sourceU i)).card + sourceLb i ≤ r
      calc
        (killSet D (sourceU i)).card + sourceLb i ≤ (r - sourceLb i) + sourceLb i :=
          Nat.add_le_add_right hk (sourceLb i)
        _ = r := Nat.sub_add_cancel (hAllLe i)
    have hZeroInKill : ∀ t : Fin r, label (D.A t) = 0 → ∀ i : Fin m, t ∈ kill i := by
      intro t ht i
      change t ∈ killSet D (sourceU i)
      simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hWU i (hLabelZero (D.A t) ht)
    have hSuccInKill : ∀ (t : Fin r) (p : Fin n), label (D.A t) = Fin.succ p →
        ∀ i : Fin m, p ∈ mask i → t ∈ kill i := by
      intro t p htp i hpm
      change t ∈ killSet D (sourceU i)
      simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hcos : D.A t + sect p ∈ W := hLabelSectCoset (D.A t) p htp
      have hA : D.A t = (D.A t + sect p) + sect p := by
        rw [add_assoc, mat3_add_self_eq_zero (sect p), add_zero]
      rw [hA]
      exact (sourceU i).add_mem ((hWU i) hcos) (hSectSource i p hpm)
    have hTermCoverage : ∀ t : Fin r,
        lambda0 ≤ ∑ i : Fin m, if t ∈ kill i then lambda i else 0 :=
      term_coverage_from_label_cover (fun t : Fin r => label (D.A t)) mask kill
        lambda lambda0 hZeroCoverage hNonzeroCoverage hZeroInKill hSuccInKill
    exact weighted_cover_infeasible_from_term_coverage kill sourceLb lambda lambda0 target
      hZeroCoverage hTermCoverage hRowsAdd hrt hCert
  · push_neg at hAllLe
    rcases hAllLe with ⟨i, hi⟩
    exact quotient_bound_exceeds_length (hWU i) D (hSource i) hi

end QiushiMatmul
