import QiushiMonotonicity
import QiushiCodeSpanCore
import QiushiOrbit10FP
import QiushiOrbit11FP

namespace QiushiMatmul

private theorem step99mono_spanCodes_le_of_gens (A B : List Nat)
    (h : ∀ n ∈ A, codeMat n ∈ spanCodes B) : spanCodes A ≤ spanCodes B := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    exact h n hn)

def monoW_30 : Submodule F2 Mat3 := spanCodes [256, 68, 16, 8, 2, 1]

theorem step99_mono_30_le_10 : monoW_30 ≤ orbit10W := by
  apply step99mono_spanCodes_le_of_gens [256, 68, 16, 8, 2, 1] [1, 2, 8, 16, 68, 160, 256]
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)

theorem step99_mono_30_lb12 : QuotientRankAtLeast monoW_30 12 :=
  quotientRankAtLeast_mono step99_mono_30_le_10 orbit10_lb12

def monoW_32 : Submodule F2 Mat3 := spanCodes [128, 32, 20, 8, 2, 1]

theorem step99_mono_32_le_11 : monoW_32 ≤ orbit11W := by
  apply step99mono_spanCodes_le_of_gens [128, 32, 20, 8, 2, 1] [1, 2, 8, 20, 32, 68, 128]
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
  · subst h4
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
  · subst h5
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 1 (by decide)

theorem step99_mono_32_lb12 : QuotientRankAtLeast monoW_32 12 :=
  quotientRankAtLeast_mono step99_mono_32_le_11 orbit11_lb12

end QiushiMatmul
