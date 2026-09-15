import Mathlib
import QiushiCodeSpanCore
import QiushiFlattenSeeds
import QiushiMonotonicity
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbitTransport
import QiushiStep81Qdim2Generated
import QiushiStep98Orbit153Mono
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiStep99Orbit237Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiTransposeTransport

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step107o373_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step107o373_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

private theorem step107o373_codeMat_mem_transposeW_of_witness
    {V : Submodule F2 Mat3} {pre tpre : Nat}
    (h_mem : codeMat tpre ∈ V)
    (h_trans : (codeMat tpre : Mat3).transpose = codeMat pre) :
    codeMat pre ∈ transposeW V := by
  change ∃ X, X ∈ V ∧ transposeLinearMap X = codeMat pre
  exact ⟨codeMat tpre, h_mem, h_trans⟩

/-- Orbit 373 quotient kernel, with original certificate-compatible labels handled elsewhere. -/
def o373W : Submodule F2 Mat3 := spanCodes [300, 224, 20, 1]

-- Source 0: original row 0, source orbit 196, lb 16, cap 0, mask 64
def step107o373ActualSource0 : Submodule F2 Mat3 := spanCodes [1, 14, 20, 224, 290]

theorem step107_o373_row0_W_le_source : o373W ≤ step107o373ActualSource0 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource0
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 14, 20, 224, 290] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 14, 20, 224, 290] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 14, 20, 224, 290] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 14, 20, 224, 290] 1 (by decide)

-- Source 1: original row 2, source orbit 196, lb 16, cap 0, mask 131072
def step107o373ActualSource1 : Submodule F2 Mat3 := spanCodes [1, 20, 68, 164, 300]

theorem step107_o373_row1_W_le_source : o373W ≤ step107o373ActualSource1 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource1
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 68, 164, 300] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 68, 164, 300] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 68, 164, 300] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 68, 164, 300] 1 (by decide)

-- Source 2: original row 3, source orbit 217, lb 16, cap 0, mask 1048576
def step107o373ActualSource2 : Submodule F2 Mat3 := spanCodes [1, 20, 74, 170, 300]

theorem step107_o373_row2_W_le_source : o373W ≤ step107o373ActualSource2 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource2
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 74, 170, 300] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 74, 170, 300] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 74, 170, 300] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 74, 170, 300] 1 (by decide)

-- Source 3: original row 7, source orbit 144, lb 15, cap 1, mask 4
def step107o373ActualSource3 : Submodule F2 Mat3 := spanCodes [1, 6, 18, 224, 298]

theorem step107_o373_row3_W_le_source : o373W ≤ step107o373ActualSource3 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource3
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 224, 298] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 224, 298] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 224, 298] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 224, 298] 1 (by decide)

-- Source 4: original row 17, source orbit 144, lb 15, cap 1, mask 32768
def step107o373ActualSource4 : Submodule F2 Mat3 := spanCodes [1, 20, 64, 160, 300]

theorem step107_o373_row4_W_le_source : o373W ≤ step107o373ActualSource4 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource4
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 64, 160, 300] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 64, 160, 300] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 64, 160, 300] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 64, 160, 300] 1 (by decide)

-- Source 5: original row 31, source orbit 65, lb 15, cap 1, mask 16842880
def step107o373ActualSource5 : Submodule F2 Mat3 := spanCodes [1, 20, 32, 66, 130, 268]

theorem step107_o373_row5_W_le_source : o373W ≤ step107o373ActualSource5 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource5
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 66, 130, 268] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 66, 130, 268] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 66, 130, 268] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 66, 130, 268] 1 (by decide)

-- Source 6: original row 37, source orbit 69, lb 15, cap 1, mask 138413056
def step107o373ActualSource6 : Submodule F2 Mat3 := spanCodes [1, 20, 38, 78, 136, 266]

theorem step107_o373_row6_W_le_source : o373W ≤ step107o373ActualSource6 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource6
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 38, 78, 136, 266] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 38, 78, 136, 266] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 38, 78, 136, 266] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 38, 78, 136, 266] 1 (by decide)

-- Source 7: original row 59, source orbit 55, lb 14, cap 2, mask 20482
def step107o373ActualSource7 : Submodule F2 Mat3 := spanCodes [1, 4, 16, 42, 202, 258]

theorem step107_o373_row7_W_le_source : o373W ≤ step107o373ActualSource7 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource7
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 202, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 202, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 202, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 202, 258] 1 (by decide)

-- Source 8: original row 100, source orbit 17, lb 14, cap 2, mask 281166352
def step107o373ActualSource8 : Submodule F2 Mat3 := spanCodes [1, 10, 20, 36, 68, 128, 258]

theorem step107_o373_row8_W_le_source : o373W ≤ step107o373ActualSource8 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource8
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 36, 68, 128, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 36, 68, 128, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 36, 68, 128, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 36, 68, 128, 258] 1 (by decide)

-- Source 9: original row 114, source orbit 55, lb 14, cap 2, mask 570425352
def step107o373ActualSource9 : Submodule F2 Mat3 := spanCodes [1, 8, 20, 100, 132, 292]

theorem step107_o373_row9_W_le_source : o373W ≤ step107o373ActualSource9 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource9
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 100, 132, 292] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 100, 132, 292] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 100, 132, 292] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 100, 132, 292] 1 (by decide)

-- Source 10: original row 160, source orbit 11, lb 12, cap 4, mask 21202
def step107o373ActualSource10 : Submodule F2 Mat3 := spanCodes [1, 4, 10, 16, 32, 192, 258]

theorem step107_o373_row10_W_le_source : o373W ≤ step107o373ActualSource10 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource10
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 192, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 192, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 192, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 192, 258] 1 (by decide)

-- Source 11: original row 194, source orbit 14, lb 12, cap 4, mask 80234500
def step107o373ActualSource11 : Submodule F2 Mat3 := spanCodes [1, 6, 18, 40, 72, 128, 258]

theorem step107_o373_row11_W_le_source : o373W ≤ step107o373ActualSource11 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource11
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 72, 128, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 72, 128, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 72, 128, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 72, 128, 258] 1 (by decide)

-- Source 12: original row 207, source orbit 14, lb 12, cap 4, mask 143724808
def step107o373ActualSource12 : Submodule F2 Mat3 := spanCodes [1, 8, 20, 34, 66, 128, 262]

theorem step107_o373_row12_W_le_source : o373W ≤ step107o373ActualSource12 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource12
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 66, 128, 262] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 66, 128, 262] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 66, 128, 262] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 66, 128, 262] 1 (by decide)

-- Source 13: original row 209, source orbit 14, lb 12, cap 4, mask 151589008
def step107o373ActualSource13 : Submodule F2 Mat3 := spanCodes [1, 10, 20, 32, 66, 130, 262]

theorem step107_o373_row13_W_le_source : o373W ≤ step107o373ActualSource13 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource13
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 32, 66, 130, 262] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 32, 66, 130, 262] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 32, 66, 130, 262] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 10, 20, 32, 66, 130, 262] 1 (by decide)

-- Source 14: original row 224, source orbit 14, lb 12, cap 4, mask 289677832
def step107o373ActualSource14 : Submodule F2 Mat3 := spanCodes [1, 8, 20, 36, 70, 130, 256]

theorem step107_o373_row14_W_le_source : o373W ≤ step107o373ActualSource14 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource14
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 36, 70, 130, 256] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 36, 70, 130, 256] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 36, 70, 130, 256] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 36, 70, 130, 256] 1 (by decide)

-- Source 15: original row 245, source orbit 11, lb 12, cap 4, mask 572655752
def step107o373ActualSource15 : Submodule F2 Mat3 := spanCodes [1, 8, 20, 32, 68, 132, 260]

theorem step107_o373_row15_W_le_source : o373W ≤ step107o373ActualSource15 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource15
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 68, 132, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 68, 132, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 68, 132, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 68, 132, 260] 1 (by decide)

-- Source 16: original row 266, source orbit 10, lb 12, cap 4, mask 1094787232
def step107o373ActualSource16 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 32, 66, 130, 256]

theorem step107_o373_row16_W_le_source : o373W ≤ step107o373ActualSource16 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource16
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 66, 130, 256] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 66, 130, 256] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 66, 130, 256] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 66, 130, 256] 1 (by decide)

-- Source 17: original row 272, source orbit 14, lb 12, cap 4, mask 1143083272
def step107o373ActualSource17 : Submodule F2 Mat3 := spanCodes [1, 8, 20, 34, 68, 134, 262]

theorem step107_o373_row17_W_le_source : o373W ≤ step107o373ActualSource17 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource17
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 68, 134, 262] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 68, 134, 262] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 68, 134, 262] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 34, 68, 134, 262] 1 (by decide)

-- Source 18: original row 273, source orbit 14, lb 12, cap 4, mask 1145309320
def step107o373ActualSource18 : Submodule F2 Mat3 := spanCodes [1, 8, 20, 32, 70, 134, 260]

theorem step107_o373_row18_W_le_source : o373W ≤ step107o373ActualSource18 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource18
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 70, 134, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 70, 134, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 70, 134, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 8, 20, 32, 70, 134, 260] 1 (by decide)

-- Source 19: original row 322, source orbit 3, lb 9, cap 7, mask 509714017
def step107o373ActualSource19 : Submodule F2 Mat3 := spanCodes [1, 2, 12, 20, 36, 64, 132, 260]

theorem step107_o373_row19_W_le_source : o373W ≤ step107o373ActualSource19 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource19
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 64, 132, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 64, 132, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 64, 132, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 64, 132, 260] 1 (by decide)

-- Source 20: original row 330, source orbit 3, lb 9, cap 7, mask 718624042
def step107o373ActualSource20 : Submodule F2 Mat3 := spanCodes [1, 4, 8, 16, 34, 66, 128, 258]

theorem step107_o373_row20_W_le_source : o373W ≤ step107o373ActualSource20 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource20
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 34, 66, 128, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 34, 66, 128, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 34, 66, 128, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 34, 66, 128, 258] 1 (by decide)

-- Source 21: original row 331, source orbit 3, lb 9, cap 7, mask 757945042
def step107o373ActualSource21 : Submodule F2 Mat3 := spanCodes [1, 4, 10, 16, 32, 66, 130, 258]

theorem step107_o373_row21_W_le_source : o373W ≤ step107o373ActualSource21 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource21
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 66, 130, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 66, 130, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 66, 130, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 32, 66, 130, 258] 1 (by decide)

-- Source 22: original row 334, source orbit 3, lb 9, cap 7, mask 885738292
def step107o373ActualSource22 : Submodule F2 Mat3 := spanCodes [1, 6, 10, 18, 34, 66, 128, 258]

theorem step107_o373_row22_W_le_source : o373W ≤ step107o373ActualSource22 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource22
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 34, 66, 128, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 34, 66, 128, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 34, 66, 128, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 34, 66, 128, 258] 1 (by decide)

-- Source 23: original row 343, source orbit 3, lb 9, cap 7, mask 1387081042
def step107o373ActualSource23 : Submodule F2 Mat3 := spanCodes [1, 4, 10, 16, 34, 66, 128, 256]

theorem step107_o373_row23_W_le_source : o373W ≤ step107o373ActualSource23 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource23
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 34, 66, 128, 256] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 34, 66, 128, 256] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 34, 66, 128, 256] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 34, 66, 128, 256] 1 (by decide)

-- Source 24: original row 5, source orbit 237, lb 16, cap 0, mask 268435456
def step107o373ActualSource24 : Submodule F2 Mat3 := spanCodes [1, 20, 106, 138, 300]

theorem step107_o373_row24_W_le_source : o373W ≤ step107o373ActualSource24 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource24
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 106, 138, 300] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 106, 138, 300] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 106, 138, 300] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 106, 138, 300] 1 (by decide)

-- Source 25: original row 9, source orbit 153, lb 15, cap 1, mask 32
def step107o373ActualSource25 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 224, 288]

theorem step107_o373_row25_W_le_source : o373W ≤ step107o373ActualSource25 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource25
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 224, 288] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 224, 288] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 224, 288] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 224, 288] 1 (by decide)

-- Source 26: original row 21, source orbit 65, lb 15, cap 1, mask 1310752
def step107o373ActualSource26 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 70, 166, 288]

theorem step107_o373_row26_W_le_source : o373W ≤ step107o373ActualSource26 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource26
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 70, 166, 288] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 70, 166, 288] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 70, 166, 288] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 70, 166, 288] 1 (by decide)

-- Source 27: original row 28, source orbit 69, lb 15, cap 1, mask 8454400
def step107o373ActualSource27 : Submodule F2 Mat3 := spanCodes [1, 20, 34, 66, 128, 270]

theorem step107_o373_row27_W_le_source : o373W ≤ step107o373ActualSource27 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource27
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 34, 66, 128, 270] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 34, 66, 128, 270] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 34, 66, 128, 270] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 34, 66, 128, 270] 1 (by decide)

-- Source 28: original row 46, source orbit 65, lb 15, cap 1, mask 1077936256
def step107o373ActualSource28 : Submodule F2 Mat3 := spanCodes [1, 20, 32, 78, 142, 268]

theorem step107_o373_row28_W_le_source : o373W ≤ step107o373ActualSource28 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource28
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 78, 142, 268] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 78, 142, 268] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 78, 142, 268] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 20, 32, 78, 142, 268] 1 (by decide)

-- Source 29: original row 50, source orbit 55, lb 14, cap 2, mask 1537
def step107o373ActualSource29 : Submodule F2 Mat3 := spanCodes [1, 2, 20, 36, 196, 264]

theorem step107_o373_row29_W_le_source : o373W ≤ step107o373ActualSource29 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource29
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 36, 196, 264] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 36, 196, 264] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 36, 196, 264] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 36, 196, 264] 1 (by decide)

-- Source 30: original row 54, source orbit 55, lb 14, cap 2, mask 5152
def step107o373ActualSource30 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 38, 198, 262]

theorem step107_o373_row30_W_le_source : o373W ≤ step107o373ActualSource30 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource30
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 38, 198, 262] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 38, 198, 262] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 38, 198, 262] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 38, 198, 262] 1 (by decide)

-- Source 31: original row 169, source orbit 10, lb 12, cap 4, mask 3440692
def step107o373ActualSource31 : Submodule F2 Mat3 := spanCodes [1, 6, 10, 18, 64, 160, 288]

theorem step107_o373_row31_W_le_source : o373W ≤ step107o373ActualSource31 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource31
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 64, 160, 288] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 64, 160, 288] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 64, 160, 288] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 10, 18, 64, 160, 288] 1 (by decide)

-- Source 32: original row 178, source orbit 10, lb 12, cap 4, mask 25264513
def step107o373ActualSource32 : Submodule F2 Mat3 := spanCodes [1, 2, 20, 32, 64, 128, 268]

theorem step107_o373_row32_W_le_source : o373W ≤ step107o373ActualSource32 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource32
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 32, 64, 128, 268] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 32, 64, 128, 268] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 32, 64, 128, 268] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 32, 64, 128, 268] 1 (by decide)

-- Source 33: original row 200, source orbit 10, lb 12, cap 4, mask 102260737
def step107o373ActualSource33 : Submodule F2 Mat3 := spanCodes [1, 2, 20, 44, 72, 132, 256]

theorem step107_o373_row33_W_le_source : o373W ≤ step107o373ActualSource33 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource33
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 44, 72, 132, 256] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 44, 72, 132, 256] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 44, 72, 132, 256] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 44, 72, 132, 256] 1 (by decide)

-- Source 34: original row 256, source orbit 14, lb 12, cap 4, mask 810025732
def step107o373ActualSource34 : Submodule F2 Mat3 := spanCodes [1, 6, 18, 34, 72, 138, 264]

theorem step107_o373_row34_W_le_source : o373W ≤ step107o373ActualSource34 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource34
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 34, 72, 138, 264] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 34, 72, 138, 264] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 34, 72, 138, 264] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 34, 72, 138, 264] 1 (by decide)

-- Source 35: original row 278, source orbit 14, lb 12, cap 4, mask 1344800002
def step107o373ActualSource35 : Submodule F2 Mat3 := spanCodes [1, 4, 16, 34, 72, 138, 266]

theorem step107_o373_row35_W_le_source : o373W ≤ step107o373ActualSource35 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource35
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 72, 138, 266] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 72, 138, 266] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 72, 138, 266] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 72, 138, 266] 1 (by decide)

-- Source 36: original row 285, source orbit 14, lb 12, cap 4, mask 1711276057
def step107o373ActualSource36 : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 100, 132, 292]

theorem step107_o373_row36_W_le_source : o373W ≤ step107o373ActualSource36 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource36
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 100, 132, 292] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 100, 132, 292] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 100, 132, 292] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 100, 132, 292] 1 (by decide)

-- Source 37: original row 321, source orbit 3, lb 9, cap 7, mask 434529817
def step107o373ActualSource37 : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 36, 68, 128, 256]

theorem step107_o373_row37_W_le_source : o373W ≤ step107o373ActualSource37 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource37
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 36, 68, 128, 256] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 36, 68, 128, 256] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 36, 68, 128, 256] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 36, 68, 128, 256] 1 (by decide)

-- Source 38: original row 25, source orbit 69, lb 15, cap 1, mask 4259872
def step107o373ActualSource38 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 66, 162, 288]

theorem step107_o373_row38_W_le_source : o373W ≤ step107o373ActualSource38 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource38
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 66, 162, 288] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 66, 162, 288] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 66, 162, 288] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 66, 162, 288] 1 (by decide)

-- Source 39: original row 55, source orbit 55, lb 14, cap 2, mask 6145
def step107o373ActualSource39 : Submodule F2 Mat3 := spanCodes [1, 2, 20, 40, 200, 260]

theorem step107_o373_row39_W_le_source : o373W ≤ step107o373ActualSource39 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource39
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 200, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 200, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 200, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 200, 260] 1 (by decide)

-- Source 40: original row 189, source orbit 14, lb 12, cap 4, mask 53495812
def step107o373ActualSource40 : Submodule F2 Mat3 := spanCodes [1, 6, 18, 40, 74, 130, 258]

theorem step107_o373_row40_W_le_source : o373W ≤ step107o373ActualSource40 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource40
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 74, 130, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 74, 130, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 74, 130, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 40, 74, 130, 258] 1 (by decide)

-- Source 41: original row 197, source orbit 14, lb 12, cap 4, mask 86528002
def step107o373ActualSource41 : Submodule F2 Mat3 := spanCodes [1, 4, 16, 42, 72, 130, 258]

theorem step107_o373_row41_W_le_source : o373W ≤ step107o373ActualSource41 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource41
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 72, 130, 258] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 72, 130, 258] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 72, 130, 258] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 42, 72, 130, 258] 1 (by decide)

-- Source 42: original row 232, source orbit 14, lb 12, cap 4, mask 402757633
def step107o373ActualSource42 : Submodule F2 Mat3 := spanCodes [1, 2, 20, 40, 64, 136, 260]

theorem step107_o373_row42_W_le_source : o373W ≤ step107o373ActualSource42 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource42
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 64, 136, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 64, 136, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 64, 136, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 20, 40, 64, 136, 260] 1 (by decide)

-- Source 43: original row 235, source orbit 14, lb 12, cap 4, mask 427819033
def step107o373ActualSource43 : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 96, 128, 292]

theorem step107_o373_row43_W_le_source : o373W ≤ step107o373ActualSource43 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource43
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 292] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 292] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 292] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 292] 1 (by decide)

-- Source 44: original row 238, source orbit 11, lb 12, cap 4, mask 545917472
def step107o373ActualSource44 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 36, 68, 128, 260]

theorem step107_o373_row44_W_le_source : o373W ≤ step107o373ActualSource44 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource44
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 68, 128, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 68, 128, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 68, 128, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 68, 128, 260] 1 (by decide)

-- Source 45: original row 253, source orbit 14, lb 12, cap 4, mask 754974802
def step107o373ActualSource45 : Submodule F2 Mat3 := spanCodes [1, 4, 10, 16, 98, 130, 290]

theorem step107_o373_row45_W_le_source : o373W ≤ step107o373ActualSource45 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource45
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 98, 130, 290] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 98, 130, 290] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 98, 130, 290] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 98, 130, 290] 1 (by decide)

-- Source 46: original row 265, source orbit 14, lb 12, cap 4, mask 1091832352
def step107o373ActualSource46 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 36, 70, 130, 260]

theorem step107_o373_row46_W_le_source : o373W ≤ step107o373ActualSource46 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource46
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 70, 130, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 70, 130, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 70, 130, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 36, 70, 130, 260] 1 (by decide)

-- Source 47: original row 277, source orbit 14, lb 12, cap 4, mask 1342515202
def step107o373ActualSource47 : Submodule F2 Mat3 := spanCodes [1, 4, 16, 40, 66, 138, 256]

theorem step107_o373_row47_W_le_source : o373W ≤ step107o373ActualSource47 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource47
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 40, 66, 138, 256] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 40, 66, 138, 256] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 40, 66, 138, 256] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 40, 66, 138, 256] 1 (by decide)

-- Source 48: original row 150, source orbit 11, lb 12, cap 4, mask 7777
def step107o373ActualSource48 : Submodule F2 Mat3 := spanCodes [1, 2, 12, 20, 36, 196, 260]

theorem step107_o373_row48_W_le_source : o373W ≤ step107o373ActualSource48 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource48
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 196, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 196, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 196, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 36, 196, 260] 1 (by decide)

-- Source 49: original row 229, source orbit 10, lb 12, cap 4, mask 336863392
def step107o373ActualSource49 : Submodule F2 Mat3 := spanCodes [1, 12, 20, 32, 70, 134, 256]

theorem step107_o373_row49_W_le_source : o373W ≤ step107o373ActualSource49 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource49
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 70, 134, 256] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 70, 134, 256] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 70, 134, 256] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 12, 20, 32, 70, 134, 256] 1 (by decide)

-- Source 50: original row 275, source orbit 10, lb 12, cap 4, mask 1212679300
def step107o373ActualSource50 : Submodule F2 Mat3 := spanCodes [1, 6, 18, 32, 72, 136, 266]

theorem step107_o373_row50_W_le_source : o373W ≤ step107o373ActualSource50 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource50
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 32, 72, 136, 266] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 32, 72, 136, 266] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 32, 72, 136, 266] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 6, 18, 32, 72, 136, 266] 1 (by decide)

-- Source 51: original row 348, source orbit 3, lb 9, cap 7, mask 1717967257
def step107o373ActualSource51 : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 32, 68, 132, 260]

theorem step107_o373_row51_W_le_source : o373W ≤ step107o373ActualSource51 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource51
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 132, 260] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 132, 260] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 132, 260] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 132, 260] 1 (by decide)

-- Source 52: original row 49, source orbit 55, lb 14, cap 2, mask 82
def step107o373ActualSource52 : Submodule F2 Mat3 := spanCodes [1, 4, 10, 16, 224, 290]

theorem step107_o373_row52_W_le_source : o373W ≤ step107o373ActualSource52 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource52
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 224, 290] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 224, 290] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 224, 290] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 10, 16, 224, 290] 1 (by decide)

-- Source 53: original row 172, source orbit 14, lb 12, cap 4, mask 5570602
def step107o373ActualSource53 : Submodule F2 Mat3 := spanCodes [1, 4, 8, 16, 66, 162, 288]

theorem step107_o373_row53_W_le_source : o373W ≤ step107o373ActualSource53 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource53
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 66, 162, 288] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 66, 162, 288] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 66, 162, 288] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 8, 16, 66, 162, 288] 1 (by decide)

-- Source 54: original row 196, source orbit 14, lb 12, cap 4, mask 84214402
def step107o373ActualSource54 : Submodule F2 Mat3 := spanCodes [1, 4, 16, 32, 66, 130, 264]

theorem step107_o373_row54_W_le_source : o373W ≤ step107o373ActualSource54 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource54
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 32, 66, 130, 264] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 32, 66, 130, 264] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 32, 66, 130, 264] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 32, 66, 130, 264] 1 (by decide)

-- Source 55: original row 236, source orbit 14, lb 12, cap 4, mask 503316577
def step107o373ActualSource55 : Submodule F2 Mat3 := spanCodes [1, 2, 12, 20, 100, 132, 288]

theorem step107_o373_row55_W_le_source : o373W ≤ step107o373ActualSource55 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource55
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 100, 132, 288] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 100, 132, 288] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 100, 132, 288] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 2, 12, 20, 100, 132, 288] 1 (by decide)

-- Source 56: original row 252, source orbit 14, lb 12, cap 4, mask 676332802
def step107o373ActualSource56 : Submodule F2 Mat3 := spanCodes [1, 4, 16, 34, 74, 136, 266]

theorem step107_o373_row56_W_le_source : o373W ≤ step107o373ActualSource56 := by
  unfold o373W
  apply step107o373_spanCodes_le_of_gens [300, 224, 20, 1] step107o373ActualSource56
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 74, 136, 266] 300 (by decide)
  · subst h1
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 74, 136, 266] 224 (by decide)
  · subst h2
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 74, 136, 266] 20 (by decide)
  · subst h3
    exact spanContainsCodeCore_implies_mem_spanCodes [1, 4, 16, 34, 74, 136, 266] 1 (by decide)

-- Dispatch for source 0: row orbit 196, theorem source 196, type action
private theorem step107o373s0_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s0_source_le_transport :
    step107o373ActualSource0 ≤ actionW (codeMat 281) (codeMat 419) o196W := by
  apply step107o373_spanCodes_le_of_gens [1, 14, 20, 224, 290]
    (actionW (codeMat 281) (codeMat 419) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 1 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 281) (codeMat 419) (codeMat 10) = codeMat 14 := by
      unfold actionA
      rw [step107o373s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 10 * (codeMat 183 : Mat3).transpose = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 43 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 281) (codeMat 419) (codeMat 43) = codeMat 20 := by
      unfold actionA
      rw [step107o373s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 43 * (codeMat 183 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 310 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide)
    have hact : actionA (codeMat 281) (codeMat 419) (codeMat 310) = codeMat 224 := by
      unfold actionA
      rw [step107o373s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 310 * (codeMat 183 : Mat3).transpose = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 435 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 435 (by decide)
    have hact : actionA (codeMat 281) (codeMat 419) (codeMat 435) = codeMat 290 := by
      unfold actionA
      rw [step107o373s0_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 435 * (codeMat 183 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row0_qr : QuotientRankAtLeast step107o373ActualSource0 16 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 419) o196W) 16 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 419) hP hQ o196W 16 step99_orbit196_lb16_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource0 16 :=
    quotientRankAtLeast_mono step107o373s0_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 1: row orbit 196, theorem source 196, type transpose
private theorem step107o373s1_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = (codeMat 417 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * (codeMat 417 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s1_source_le_transport :
    step107o373ActualSource1 ≤ transposeW (actionW (codeMat 489) (codeMat 177) o196W) := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 68, 164, 300]
    (transposeW (actionW (codeMat 489) (codeMat 177) o196W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 1 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 489) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s1_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 1 * (codeMat 417 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 489) (codeMat 177) o196W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    have hw : codeMat 441 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 441 (by decide)
    have hact : actionA (codeMat 489) (codeMat 177) (codeMat 441) = codeMat 80 := by
      unfold actionA
      rw [step107o373s1_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 441 * (codeMat 417 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 489) (codeMat 177) o196W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    have hw : codeMat 11 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 489) (codeMat 177) (codeMat 11) = codeMat 68 := by
      unfold actionA
      rw [step107o373s1_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 11 * (codeMat 417 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 68 ∈ actionW (codeMat 489) (codeMat 177) o196W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 68 : Mat3).transpose = codeMat 68 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    have hw : codeMat 175 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 175 (by decide)
    have hact : actionA (codeMat 489) (codeMat 177) (codeMat 175) = codeMat 224 := by
      unfold actionA
      rw [step107o373s1_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 175 * (codeMat 417 : Mat3).transpose = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 224 ∈ actionW (codeMat 489) (codeMat 177) o196W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 224 : Mat3).transpose = codeMat 164 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    have hw : codeMat 43 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 489) (codeMat 177) (codeMat 43) = codeMat 450 := by
      unfold actionA
      rw [step107o373s1_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 43 * (codeMat 417 : Mat3).transpose = codeMat 450
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 450 ∈ actionW (codeMat 489) (codeMat 177) o196W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 450 : Mat3).transpose = codeMat 300 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step107_o373_row1_qr : QuotientRankAtLeast step107o373ActualSource1 16 := by
  have hP : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 489) (codeMat 177) o196W) 16 :=
    @quotientRankAtLeast_action (codeMat 489) (codeMat 177) hP hQ o196W 16 step99_orbit196_lb16_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 489) (codeMat 177) o196W)) 16 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step107o373ActualSource1 16 :=
    quotientRankAtLeast_mono step107o373s1_source_le_transport hT
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 2: row orbit 217, theorem source 217, type action
private theorem step107o373s2_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s2_source_le_transport :
    step107o373ActualSource2 ≤ actionW (codeMat 185) (codeMat 273) o217W := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 74, 170, 300]
    (actionW (codeMat 185) (codeMat 273) o217W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 1 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s2_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 132 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 132 (by decide)
    have hact : actionA (codeMat 185) (codeMat 273) (codeMat 132) = codeMat 20 := by
      unfold actionA
      rw [step107o373s2_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 132 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 185) (codeMat 273) (codeMat 11) = codeMat 74 := by
      unfold actionA
      rw [step107o373s2_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 11 * (codeMat 273 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 464 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 464 (by decide)
    have hact : actionA (codeMat 185) (codeMat 273) (codeMat 464) = codeMat 170 := by
      unfold actionA
      rw [step107o373s2_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 464 * (codeMat 273 : Mat3).transpose = codeMat 170
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 185) (codeMat 273) (codeMat 96) = codeMat 300 := by
      unfold actionA
      rw [step107o373s2_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 300
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row2_qr : QuotientRankAtLeast step107o373ActualSource2 16 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 273) o217W) 16 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 273) hP hQ o217W 16 step99_orbit217_lb16_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource2 16 :=
    quotientRankAtLeast_mono step107o373s2_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 3: row orbit 144, theorem source 144, type action
private theorem step107o373s3_QtInv :
    (codeMat 428 : Mat3).transpose⁻¹ = (codeMat 107 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 428 : Mat3).transpose * (codeMat 107 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s3_source_le_transport :
    step107o373ActualSource3 ≤ actionW (codeMat 345) (codeMat 428) o144W := by
  apply step107o373_spanCodes_le_of_gens [1, 6, 18, 224, 298]
    (actionW (codeMat 345) (codeMat 428) o144W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 2 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 345) (codeMat 428) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step107o373s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 2 * (codeMat 107 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 3 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 345) (codeMat 428) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step107o373s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 3 * (codeMat 107 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 345) (codeMat 428) (codeMat 32) = codeMat 18 := by
      unfold actionA
      rw [step107o373s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 32 * (codeMat 107 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 441 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 345) (codeMat 428) (codeMat 441) = codeMat 224 := by
      unfold actionA
      rw [step107o373s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 441 * (codeMat 107 : Mat3).transpose = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 494 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 494 (by decide)
    have hact : actionA (codeMat 345) (codeMat 428) (codeMat 494) = codeMat 298 := by
      unfold actionA
      rw [step107o373s3_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 494 * (codeMat 107 : Mat3).transpose = codeMat 298
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row3_qr : QuotientRankAtLeast step107o373ActualSource3 15 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 428 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 428) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 428) hP hQ o144W 15 step99_orbit144_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource3 15 :=
    quotientRankAtLeast_mono step107o373s3_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 4: row orbit 144, theorem source 144, type transpose
private theorem step107o373s4_QtInv :
    (codeMat 157 : Mat3).transpose⁻¹ = (codeMat 486 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 157 : Mat3).transpose * (codeMat 486 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s4_source_le_transport :
    step107o373ActualSource4 ≤ transposeW (actionW (codeMat 169) (codeMat 157) o144W) := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 64, 160, 300]
    (transposeW (actionW (codeMat 169) (codeMat 157) o144W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 3 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 169) (codeMat 157) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step107o373s4_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 3 * (codeMat 486 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 169) (codeMat 157) o144W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    have hw : codeMat 411 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 169) (codeMat 157) (codeMat 411) = codeMat 80 := by
      unfold actionA
      rw [step107o373s4_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 411 * (codeMat 486 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 169) (codeMat 157) o144W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    have hw : codeMat 1 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 157) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step107o373s4_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * (codeMat 486 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 4 ∈ actionW (codeMat 169) (codeMat 157) o144W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 4 : Mat3).transpose = codeMat 64 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    have hw : codeMat 118 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 118 (by decide)
    have hact : actionA (codeMat 169) (codeMat 157) (codeMat 118) = codeMat 160 := by
      unfold actionA
      rw [step107o373s4_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 118 * (codeMat 486 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 160 ∈ actionW (codeMat 169) (codeMat 157) o144W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 160 : Mat3).transpose = codeMat 160 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    have hw : codeMat 34 ∈ o144W :=
      spanContainsCodeCore_implies_mem_spanCodes [408, 84, 32, 2, 1] 34 (by decide)
    have hact : actionA (codeMat 169) (codeMat 157) (codeMat 34) = codeMat 450 := by
      unfold actionA
      rw [step107o373s4_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 34 * (codeMat 486 : Mat3).transpose = codeMat 450
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 450 ∈ actionW (codeMat 169) (codeMat 157) o144W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 450 : Mat3).transpose = codeMat 300 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step107_o373_row4_qr : QuotientRankAtLeast step107o373ActualSource4 15 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 157) o144W) 15 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 157) hP hQ o144W 15 step99_orbit144_lb15_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 169) (codeMat 157) o144W)) 15 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step107o373ActualSource4 15 :=
    quotientRankAtLeast_mono step107o373s4_source_le_transport hT
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 5: row orbit 65, theorem source 65, type action
private theorem step107o373s5_QtInv :
    (codeMat 225 : Mat3).transpose⁻¹ = (codeMat 169 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 225 : Mat3).transpose * (codeMat 169 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s5_source_le_transport :
    step107o373ActualSource5 ≤ actionW (codeMat 84) (codeMat 225) o65W := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 32, 66, 130, 268]
    (actionW (codeMat 84) (codeMat 225) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 84) (codeMat 225) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step107o373s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 320 * (codeMat 169 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 225) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step107o373s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 169 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 225) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step107o373s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 169 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 261 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 261 (by decide)
    have hact : actionA (codeMat 84) (codeMat 225) (codeMat 261) = codeMat 66 := by
      unfold actionA
      rw [step107o373s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 261 * (codeMat 169 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 84) (codeMat 225) (codeMat 260) = codeMat 130 := by
      unfold actionA
      rw [step107o373s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 260 * (codeMat 169 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 84) (codeMat 225) (codeMat 170) = codeMat 268 := by
      unfold actionA
      rw [step107o373s5_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 170 * (codeMat 169 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row5_qr : QuotientRankAtLeast step107o373ActualSource5 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 225) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 225) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource5 15 :=
    quotientRankAtLeast_mono step107o373s5_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 6: row orbit 69, theorem source 69, type action
private theorem step107o373s6_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = (codeMat 407 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * (codeMat 407 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s6_source_le_transport :
    step107o373ActualSource6 ≤ actionW (codeMat 377) (codeMat 405) o69W := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 38, 78, 136, 266]
    (actionW (codeMat 377) (codeMat 405) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 377) (codeMat 405) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s6_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 1 * (codeMat 407 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 437 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 437 (by decide)
    have hact : actionA (codeMat 377) (codeMat 405) (codeMat 437) = codeMat 20 := by
      unfold actionA
      rw [step107o373s6_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 437 * (codeMat 407 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 363 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 363 (by decide)
    have hact : actionA (codeMat 377) (codeMat 405) (codeMat 363) = codeMat 38 := by
      unfold actionA
      rw [step107o373s6_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 363 * (codeMat 407 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 377) (codeMat 405) (codeMat 10) = codeMat 78 := by
      unfold actionA
      rw [step107o373s6_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 10 * (codeMat 407 : Mat3).transpose = codeMat 78
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 462 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 377) (codeMat 405) (codeMat 462) = codeMat 136 := by
      unfold actionA
      rw [step107o373s6_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 462 * (codeMat 407 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 267 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 267 (by decide)
    have hact : actionA (codeMat 377) (codeMat 405) (codeMat 267) = codeMat 266 := by
      unfold actionA
      rw [step107o373s6_QtInv]
      show (codeMat 377 : Mat3).transpose * codeMat 267 * (codeMat 407 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row6_qr : QuotientRankAtLeast step107o373ActualSource6 15 := by
  have hP : Invertible (codeMat 377 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 377) (codeMat 405) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 377) (codeMat 405) hP hQ o69W 15 step99_orbit69_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource6 15 :=
    quotientRankAtLeast_mono step107o373s6_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 7: row orbit 55, theorem source 55, type action
private theorem step107o373s7_QtInv :
    (codeMat 171 : Mat3).transpose⁻¹ = (codeMat 485 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 171 : Mat3).transpose * (codeMat 485 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s7_source_le_transport :
    step107o373ActualSource7 ≤ actionW (codeMat 345) (codeMat 171) o55W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 16, 42, 202, 258]
    (actionW (codeMat 345) (codeMat 171) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 345) (codeMat 171) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step107o373s7_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 3 * (codeMat 485 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 345) (codeMat 171) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step107o373s7_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 2 * (codeMat 485 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 345) (codeMat 171) (codeMat 45) = codeMat 16 := by
      unfold actionA
      rw [step107o373s7_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 45 * (codeMat 485 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 345) (codeMat 171) (codeMat 12) = codeMat 42 := by
      unfold actionA
      rw [step107o373s7_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 12 * (codeMat 485 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 408 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 408 (by decide)
    have hact : actionA (codeMat 345) (codeMat 171) (codeMat 408) = codeMat 202 := by
      unfold actionA
      rw [step107o373s7_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 408 * (codeMat 485 : Mat3).transpose = codeMat 202
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 135 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 345) (codeMat 171) (codeMat 135) = codeMat 258 := by
      unfold actionA
      rw [step107o373s7_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 135 * (codeMat 485 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row7_qr : QuotientRankAtLeast step107o373ActualSource7 14 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 171 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 171) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 171) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource7 14 :=
    quotientRankAtLeast_mono step107o373s7_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 8: row orbit 17, theorem source 17, type action
private theorem step107o373s8_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s8_source_le_transport :
    step107o373ActualSource8 ≤ actionW (codeMat 84) (codeMat 270) step81o17s4Wspan := by
  apply step107o373_spanCodes_le_of_gens [1, 10, 20, 36, 68, 128, 258]
    (actionW (codeMat 84) (codeMat 270) step81o17s4Wspan)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 80) = codeMat 10 := by
      unfold actionA
      rw [step107o373s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 298 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 328 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 328) = codeMat 20 := by
      unfold actionA
      rw [step107o373s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 328 * (codeMat 298 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 360) = codeMat 36 := by
      unfold actionA
      rw [step107o373s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 360 * (codeMat 298 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 322 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 322 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 322) = codeMat 68 := by
      unfold actionA
      rw [step107o373s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 322 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step107o373s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 69 ∈ step81o17s4Wspan :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 84) (codeMat 270) (codeMat 69) = codeMat 258 := by
      unfold actionA
      rw [step107o373s8_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 69 * (codeMat 298 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row8_qr : QuotientRankAtLeast step107o373ActualSource8 14 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 270) step81o17s4Wspan) 14 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 270) hP hQ step81o17s4Wspan 14 step81o17s4Span_lb
  have hMono : QuotientRankAtLeast step107o373ActualSource8 14 :=
    quotientRankAtLeast_mono step107o373s8_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 9: row orbit 55, theorem source 55, type transpose
private theorem step107o373s9_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s9_source_le_transport :
    step107o373ActualSource9 ≤ transposeW (actionW (codeMat 425) (codeMat 281) o55W) := by
  apply step107o373_spanCodes_le_of_gens [1, 8, 20, 100, 132, 292]
    (transposeW (actionW (codeMat 425) (codeMat 281) o55W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 425) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step107o373s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 425) (codeMat 281) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 425) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step107o373s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 2 ∈ actionW (codeMat 425) (codeMat 281) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 2 : Mat3).transpose = codeMat 8 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    have hw : codeMat 137 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 137 (by decide)
    have hact : actionA (codeMat 425) (codeMat 281) (codeMat 137) = codeMat 80 := by
      unfold actionA
      rw [step107o373s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 137 * (codeMat 281 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 425) (codeMat 281) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    have hw : codeMat 13 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 425) (codeMat 281) (codeMat 13) = codeMat 196 := by
      unfold actionA
      rw [step107o373s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 13 * (codeMat 281 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 196 ∈ actionW (codeMat 425) (codeMat 281) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 196 : Mat3).transpose = codeMat 100 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    have hw : codeMat 319 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 319 (by decide)
    have hact : actionA (codeMat 425) (codeMat 281) (codeMat 319) = codeMat 96 := by
      unfold actionA
      rw [step107o373s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 319 * (codeMat 281 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 96 ∈ actionW (codeMat 425) (codeMat 281) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 96 : Mat3).transpose = codeMat 132 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 425) (codeMat 281) (codeMat 45) = codeMat 448 := by
      unfold actionA
      rw [step107o373s9_QtInv]
      show (codeMat 425 : Mat3).transpose * codeMat 45 * (codeMat 281 : Mat3).transpose = codeMat 448
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 448 ∈ actionW (codeMat 425) (codeMat 281) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 448 : Mat3).transpose = codeMat 292 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step107_o373_row9_qr : QuotientRankAtLeast step107o373ActualSource9 14 := by
  have hP : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 425) (codeMat 281) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 425) (codeMat 281) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 425) (codeMat 281) o55W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step107o373ActualSource9 14 :=
    quotientRankAtLeast_mono step107o373s9_source_le_transport hT
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 10: row orbit 11, theorem source 11, type action
private theorem step107o373s10_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s10_source_le_transport :
    step107o373ActualSource10 ≤ actionW (codeMat 275) (codeMat 204) orbit11W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 10, 16, 32, 192, 258]
    (actionW (codeMat 275) (codeMat 204) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 54 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 54 (by decide)
    have hact : actionA (codeMat 275) (codeMat 204) (codeMat 54) = codeMat 1 := by
      unfold actionA
      rw [step107o373s10_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 54 * (codeMat 114 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 9 (by decide)
    have hact : actionA (codeMat 275) (codeMat 204) (codeMat 9) = codeMat 4 := by
      unfold actionA
      rw [step107o373s10_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 9 * (codeMat 114 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 20 (by decide)
    have hact : actionA (codeMat 275) (codeMat 204) (codeMat 20) = codeMat 10 := by
      unfold actionA
      rw [step107o373s10_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 20 * (codeMat 114 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 275) (codeMat 204) (codeMat 32) = codeMat 16 := by
      unfold actionA
      rw [step107o373s10_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 32 * (codeMat 114 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 8 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 8 (by decide)
    have hact : actionA (codeMat 275) (codeMat 204) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step107o373s10_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 8 * (codeMat 114 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 275) (codeMat 204) (codeMat 128) = codeMat 192 := by
      unfold actionA
      rw [step107o373s10_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 128 * (codeMat 114 : Mat3).transpose = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 100 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 100 (by decide)
    have hact : actionA (codeMat 275) (codeMat 204) (codeMat 100) = codeMat 258 := by
      unfold actionA
      rw [step107o373s10_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 100 * (codeMat 114 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row10_qr : QuotientRankAtLeast step107o373ActualSource10 12 := by
  have hP : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 275) (codeMat 204) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 275) (codeMat 204) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource10 12 :=
    quotientRankAtLeast_mono step107o373s10_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 11: row orbit 14, theorem source 14, type action
private theorem step107o373s11_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s11_source_le_transport :
    step107o373ActualSource11 ≤ actionW (codeMat 103) (codeMat 270) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 6, 18, 40, 72, 128, 258]
    (actionW (codeMat 103) (codeMat 270) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 103) (codeMat 270) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s11_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 128 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 103) (codeMat 270) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step107o373s11_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 256 * (codeMat 298 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 103) (codeMat 270) (codeMat 9) = codeMat 18 := by
      unfold actionA
      rw [step107o373s11_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 9 * (codeMat 298 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 103) (codeMat 270) (codeMat 511) = codeMat 40 := by
      unfold actionA
      rw [step107o373s11_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 511 * (codeMat 298 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 103) (codeMat 270) (codeMat 130) = codeMat 72 := by
      unfold actionA
      rw [step107o373s11_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 130 * (codeMat 298 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 103) (codeMat 270) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [step107o373s11_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 8 * (codeMat 298 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 103) (codeMat 270) (codeMat 104) = codeMat 258 := by
      unfold actionA
      rw [step107o373s11_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 104 * (codeMat 298 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row11_qr : QuotientRankAtLeast step107o373ActualSource11 12 := by
  have hP : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 103) (codeMat 270) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 103) (codeMat 270) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource11 12 :=
    quotientRankAtLeast_mono step107o373s11_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 12: row orbit 14, theorem source 14, type action
private theorem step107o373s12_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s12_source_le_transport :
    step107o373ActualSource12 ≤ actionW (codeMat 331) (codeMat 423) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 8, 20, 34, 66, 128, 262]
    (actionW (codeMat 331) (codeMat 423) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 331) (codeMat 423) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step107o373s12_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 8 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 331) (codeMat 423) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [step107o373s12_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 9 * (codeMat 181 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 331) (codeMat 423) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step107o373s12_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 21 * (codeMat 181 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 23 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 23 (by decide)
    have hact : actionA (codeMat 331) (codeMat 423) (codeMat 23) = codeMat 34 := by
      unfold actionA
      rw [step107o373s12_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 23 * (codeMat 181 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 331) (codeMat 423) (codeMat 96) = codeMat 66 := by
      unfold actionA
      rw [step107o373s12_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 96 * (codeMat 181 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 331) (codeMat 423) (codeMat 360) = codeMat 128 := by
      unfold actionA
      rw [step107o373s12_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 360 * (codeMat 181 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 488 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 488 (by decide)
    have hact : actionA (codeMat 331) (codeMat 423) (codeMat 488) = codeMat 262 := by
      unfold actionA
      rw [step107o373s12_QtInv]
      show (codeMat 331 : Mat3).transpose * codeMat 488 * (codeMat 181 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row12_qr : QuotientRankAtLeast step107o373ActualSource12 12 := by
  have hP : Invertible (codeMat 331 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 331) (codeMat 423) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 331) (codeMat 423) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource12 12 :=
    quotientRankAtLeast_mono step107o373s12_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 13: row orbit 14, theorem source 14, type action
private theorem step107o373s13_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = (codeMat 179 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * (codeMat 179 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s13_source_le_transport :
    step107o373ActualSource13 ≤ actionW (codeMat 334) (codeMat 421) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 10, 20, 32, 66, 130, 262]
    (actionW (codeMat 334) (codeMat 421) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step107o373s13_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 8 * (codeMat 179 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 105) = codeMat 10 := by
      unfold actionA
      rw [step107o373s13_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 105 * (codeMat 179 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 284 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 284 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 284) = codeMat 20 := by
      unfold actionA
      rw [step107o373s13_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 284 * (codeMat 179 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 511) = codeMat 32 := by
      unfold actionA
      rw [step107o373s13_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 511 * (codeMat 179 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step107o373s13_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 104 * (codeMat 179 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 256) = codeMat 130 := by
      unfold actionA
      rw [step107o373s13_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 256 * (codeMat 179 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 480 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 480 (by decide)
    have hact : actionA (codeMat 334) (codeMat 421) (codeMat 480) = codeMat 262 := by
      unfold actionA
      rw [step107o373s13_QtInv]
      show (codeMat 334 : Mat3).transpose * codeMat 480 * (codeMat 179 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row13_qr : QuotientRankAtLeast step107o373ActualSource13 12 := by
  have hP : Invertible (codeMat 334 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 334) (codeMat 421) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 334) (codeMat 421) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource13 12 :=
    quotientRankAtLeast_mono step107o373s13_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 14: row orbit 14, theorem source 14, type action
private theorem step107o373s14_QtInv :
    (codeMat 158 : Mat3).transpose⁻¹ = (codeMat 358 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 158 : Mat3).transpose * (codeMat 358 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s14_source_le_transport :
    step107o373ActualSource14 ≤ actionW (codeMat 163) (codeMat 158) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 8, 20, 36, 70, 130, 256]
    (actionW (codeMat 163) (codeMat 158) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 163) (codeMat 158) (codeMat 130) = codeMat 1 := by
      unfold actionA
      rw [step107o373s14_QtInv]
      show (codeMat 163 : Mat3).transpose * codeMat 130 * (codeMat 358 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 163) (codeMat 158) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step107o373s14_QtInv]
      show (codeMat 163 : Mat3).transpose * codeMat 128 * (codeMat 358 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 385 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 385 (by decide)
    have hact : actionA (codeMat 163) (codeMat 158) (codeMat 385) = codeMat 20 := by
      unfold actionA
      rw [step107o373s14_QtInv]
      show (codeMat 163 : Mat3).transpose * codeMat 385 * (codeMat 358 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 163) (codeMat 158) (codeMat 1) = codeMat 36 := by
      unfold actionA
      rw [step107o373s14_QtInv]
      show (codeMat 163 : Mat3).transpose * codeMat 1 * (codeMat 358 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 406 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 406 (by decide)
    have hact : actionA (codeMat 163) (codeMat 158) (codeMat 406) = codeMat 70 := by
      unfold actionA
      rw [step107o373s14_QtInv]
      show (codeMat 163 : Mat3).transpose * codeMat 406 * (codeMat 358 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 163) (codeMat 158) (codeMat 511) = codeMat 130 := by
      unfold actionA
      rw [step107o373s14_QtInv]
      show (codeMat 163 : Mat3).transpose * codeMat 511 * (codeMat 358 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 163) (codeMat 158) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step107o373s14_QtInv]
      show (codeMat 163 : Mat3).transpose * codeMat 8 * (codeMat 358 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row14_qr : QuotientRankAtLeast step107o373ActualSource14 12 := by
  have hP : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 163) (codeMat 158) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 163) (codeMat 158) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource14 12 :=
    quotientRankAtLeast_mono step107o373s14_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 15: row orbit 11, theorem source 11, type action
private theorem step107o373s15_QtInv :
    (codeMat 188 : Mat3).transpose⁻¹ = (codeMat 103 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 188 : Mat3).transpose * (codeMat 103 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s15_source_le_transport :
    step107o373ActualSource15 ≤ actionW (codeMat 98) (codeMat 188) orbit11W := by
  apply step107o373_spanCodes_le_of_gens [1, 8, 20, 32, 68, 132, 260]
    (actionW (codeMat 98) (codeMat 188) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 188) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s15_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 103 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 98) (codeMat 188) (codeMat 2) = codeMat 8 := by
      unfold actionA
      rw [step107o373s15_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 2 * (codeMat 103 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 198 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 198 (by decide)
    have hact : actionA (codeMat 98) (codeMat 188) (codeMat 198) = codeMat 20 := by
      unfold actionA
      rw [step107o373s15_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 198 * (codeMat 103 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 98) (codeMat 188) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step107o373s15_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 3 * (codeMat 103 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 208 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 208 (by decide)
    have hact : actionA (codeMat 98) (codeMat 188) (codeMat 208) = codeMat 68 := by
      unfold actionA
      rw [step107o373s15_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 208 * (codeMat 103 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 240 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 240 (by decide)
    have hact : actionA (codeMat 98) (codeMat 188) (codeMat 240) = codeMat 132 := by
      unfold actionA
      rw [step107o373s15_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 240 * (codeMat 103 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 216 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 216 (by decide)
    have hact : actionA (codeMat 98) (codeMat 188) (codeMat 216) = codeMat 260 := by
      unfold actionA
      rw [step107o373s15_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 216 * (codeMat 103 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row15_qr : QuotientRankAtLeast step107o373ActualSource15 12 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 188 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 188) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 188) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource15 12 :=
    quotientRankAtLeast_mono step107o373s15_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 16: row orbit 10, theorem source 10, type action
private theorem step107o373s16_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s16_source_le_transport :
    step107o373ActualSource16 ≤ actionW (codeMat 84) (codeMat 226) orbit10W := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 32, 66, 130, 256]
    (actionW (codeMat 84) (codeMat 226) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 226) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 141 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 226) (codeMat 160) = codeMat 12 := by
      unfold actionA
      rw [step107o373s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 141 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 168 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 168 (by decide)
    have hact : actionA (codeMat 84) (codeMat 226) (codeMat 168) = codeMat 20 := by
      unfold actionA
      rw [step107o373s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 168 * (codeMat 141 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 226) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step107o373s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 141 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 84) (codeMat 226) (codeMat 324) = codeMat 66 := by
      unfold actionA
      rw [step107o373s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 141 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 226) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step107o373s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 141 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 226) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step107o373s16_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row16_qr : QuotientRankAtLeast step107o373ActualSource16 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 226) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 226) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource16 12 :=
    quotientRankAtLeast_mono step107o373s16_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 17: row orbit 14, theorem source 14, type action
private theorem step107o373s17_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s17_source_le_transport :
    step107o373ActualSource17 ≤ actionW (codeMat 467) (codeMat 417) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 8, 20, 34, 68, 134, 262]
    (actionW (codeMat 467) (codeMat 417) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 467) (codeMat 417) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step107o373s17_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 9 * (codeMat 177 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 467) (codeMat 417) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step107o373s17_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 8 * (codeMat 177 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 22 (by decide)
    have hact : actionA (codeMat 467) (codeMat 417) (codeMat 22) = codeMat 20 := by
      unfold actionA
      rw [step107o373s17_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 22 * (codeMat 177 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 467) (codeMat 417) (codeMat 20) = codeMat 34 := by
      unfold actionA
      rw [step107o373s17_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 20 * (codeMat 177 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 119 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 119 (by decide)
    have hact : actionA (codeMat 467) (codeMat 417) (codeMat 119) = codeMat 68 := by
      unfold actionA
      rw [step107o373s17_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 119 * (codeMat 177 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 278 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 278 (by decide)
    have hact : actionA (codeMat 467) (codeMat 417) (codeMat 278) = codeMat 134 := by
      unfold actionA
      rw [step107o373s17_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 278 * (codeMat 177 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 404 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 404 (by decide)
    have hact : actionA (codeMat 467) (codeMat 417) (codeMat 404) = codeMat 262 := by
      unfold actionA
      rw [step107o373s17_QtInv]
      show (codeMat 467 : Mat3).transpose * codeMat 404 * (codeMat 177 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row17_qr : QuotientRankAtLeast step107o373ActualSource17 12 := by
  have hP : Invertible (codeMat 467 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 467) (codeMat 417) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 467) (codeMat 417) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource17 12 :=
    quotientRankAtLeast_mono step107o373s17_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 18: row orbit 14, theorem source 14, type action
private theorem step107o373s18_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s18_source_le_transport :
    step107o373ActualSource18 ≤ actionW (codeMat 474) (codeMat 161) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 8, 20, 32, 70, 134, 260]
    (actionW (codeMat 474) (codeMat 161) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 474) (codeMat 161) (codeMat 9) = codeMat 1 := by
      unfold actionA
      rw [step107o373s18_QtInv]
      show (codeMat 474 : Mat3).transpose * codeMat 9 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 474) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step107o373s18_QtInv]
      show (codeMat 474 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 22 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 22 (by decide)
    have hact : actionA (codeMat 474) (codeMat 161) (codeMat 22) = codeMat 20 := by
      unfold actionA
      rw [step107o373s18_QtInv]
      show (codeMat 474 : Mat3).transpose * codeMat 22 * (codeMat 161 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 474) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step107o373s18_QtInv]
      show (codeMat 474 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 126 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 126 (by decide)
    have hact : actionA (codeMat 474) (codeMat 161) (codeMat 126) = codeMat 70 := by
      unfold actionA
      rw [step107o373s18_QtInv]
      show (codeMat 474 : Mat3).transpose * codeMat 126 * (codeMat 161 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 278 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 278 (by decide)
    have hact : actionA (codeMat 474) (codeMat 161) (codeMat 278) = codeMat 134 := by
      unfold actionA
      rw [step107o373s18_QtInv]
      show (codeMat 474 : Mat3).transpose * codeMat 278 * (codeMat 161 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 474) (codeMat 161) (codeMat 130) = codeMat 260 := by
      unfold actionA
      rw [step107o373s18_QtInv]
      show (codeMat 474 : Mat3).transpose * codeMat 130 * (codeMat 161 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row18_qr : QuotientRankAtLeast step107o373ActualSource18 12 := by
  have hP : Invertible (codeMat 474 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 474) (codeMat 161) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 474) (codeMat 161) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource18 12 :=
    quotientRankAtLeast_mono step107o373s18_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 19: row orbit 3, theorem source 3, type action
private theorem step107o373s19_QtInv :
    (codeMat 444 : Mat3).transpose⁻¹ = (codeMat 110 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 444 : Mat3).transpose * (codeMat 110 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s19_source_le_transport :
    step107o373ActualSource19 ≤ actionW (codeMat 84) (codeMat 444) flatW_3 := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 12, 20, 36, 64, 132, 260]
    (actionW (codeMat 84) (codeMat 444) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 110 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 110 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 464 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 464 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 464) = codeMat 12 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 464 * (codeMat 110 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 496 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 496 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 496) = codeMat 20 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 496 * (codeMat 110 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 504 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 504) = codeMat 36 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 504 * (codeMat 110 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 110 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 454 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 454 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 454) = codeMat 132 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 454 * (codeMat 110 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 455 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 455 (by decide)
    have hact : actionA (codeMat 84) (codeMat 444) (codeMat 455) = codeMat 260 := by
      unfold actionA
      rw [step107o373s19_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 455 * (codeMat 110 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row19_qr : QuotientRankAtLeast step107o373ActualSource19 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 444 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 444) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 444) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step107o373ActualSource19 9 :=
    quotientRankAtLeast_mono step107o373s19_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 20: row orbit 3, theorem source 3, type action
private theorem step107o373s20_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s20_source_le_transport :
    step107o373ActualSource20 ≤ actionW (codeMat 84) (codeMat 354) flatW_3 := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 8, 16, 34, 66, 128, 258]
    (actionW (codeMat 84) (codeMat 354) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 142 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 142 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 112) = codeMat 34 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 142 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 68 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 68) = codeMat 66 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 142 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 354) (codeMat 70) = codeMat 258 := by
      unfold actionA
      rw [step107o373s20_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 142 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row20_qr : QuotientRankAtLeast step107o373ActualSource20 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 354) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 354) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step107o373ActualSource20 9 :=
    quotientRankAtLeast_mono step107o373s20_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 21: row orbit 3, theorem source 3, type action
private theorem step107o373s21_QtInv :
    (codeMat 458 : Mat3).transpose⁻¹ = (codeMat 458 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 458 : Mat3).transpose * (codeMat 458 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s21_source_le_transport :
    step107o373ActualSource21 ≤ actionW (codeMat 84) (codeMat 458) flatW_3 := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 10, 16, 32, 66, 130, 258]
    (actionW (codeMat 84) (codeMat 458) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 458 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 458 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 368) = codeMat 10 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 458 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 40) = codeMat 16 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 458 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 32) = codeMat 32 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 458 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 326) = codeMat 66 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 458 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 325) = codeMat 130 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 458 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 324 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 324 (by decide)
    have hact : actionA (codeMat 84) (codeMat 458) (codeMat 324) = codeMat 258 := by
      unfold actionA
      rw [step107o373s21_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 458 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row21_qr : QuotientRankAtLeast step107o373ActualSource21 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 458 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 458) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 458) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step107o373ActualSource21 9 :=
    quotientRankAtLeast_mono step107o373s21_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 22: row orbit 3, theorem source 3, type action
private theorem step107o373s22_QtInv :
    (codeMat 382 : Mat3).transpose⁻¹ = (codeMat 499 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 382 : Mat3).transpose * (codeMat 499 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s22_source_le_transport :
    step107o373ActualSource22 ≤ actionW (codeMat 84) (codeMat 382) flatW_3 := by
  apply step107o373_spanCodes_le_of_gens [1, 6, 10, 18, 34, 66, 128, 258]
    (actionW (codeMat 84) (codeMat 382) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 499 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 256) = codeMat 6 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 499 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 240 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 240 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 240) = codeMat 10 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 240 * (codeMat 499 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 216) = codeMat 18 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 499 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 248 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 248 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 248) = codeMat 34 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 248 * (codeMat 499 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 198 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 198 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 198) = codeMat 66 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 198 * (codeMat 499 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 3) = codeMat 128 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 499 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 199 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 199 (by decide)
    have hact : actionA (codeMat 84) (codeMat 382) (codeMat 199) = codeMat 258 := by
      unfold actionA
      rw [step107o373s22_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 199 * (codeMat 499 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row22_qr : QuotientRankAtLeast step107o373ActualSource22 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 382 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 382) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 382) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step107o373ActualSource22 9 :=
    quotientRankAtLeast_mono step107o373s22_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 23: row orbit 3, theorem source 3, type action
private theorem step107o373s23_QtInv :
    (codeMat 106 : Mat3).transpose⁻¹ = (codeMat 396 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 106 : Mat3).transpose * (codeMat 396 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s23_source_le_transport :
    step107o373ActualSource23 ≤ actionW (codeMat 84) (codeMat 106) flatW_3 := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 10, 16, 34, 66, 128, 256]
    (actionW (codeMat 84) (codeMat 106) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 396 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 396 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 112 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 112 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 112) = codeMat 10 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 112 * (codeMat 396 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 396 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 80 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 80 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 80) = codeMat 34 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 80 * (codeMat 396 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 70 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 70 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 70) = codeMat 66 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 70 * (codeMat 396 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 396 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 106) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step107o373s23_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 396 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row23_qr : QuotientRankAtLeast step107o373ActualSource23 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 106) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 106) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step107o373ActualSource23 9 :=
    quotientRankAtLeast_mono step107o373s23_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 24: row orbit 237, theorem source 237, type action
private theorem step107o373s24_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s24_source_le_transport :
    step107o373ActualSource24 ≤ actionW (codeMat 489) (codeMat 167) o237W := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 106, 138, 300]
    (actionW (codeMat 489) (codeMat 167) o237W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 1 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 1 (by decide)
    have hact : actionA (codeMat 489) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s24_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 1 * (codeMat 167 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 363 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 363 (by decide)
    have hact : actionA (codeMat 489) (codeMat 167) (codeMat 363) = codeMat 20 := by
      unfold actionA
      rw [step107o373s24_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 363 * (codeMat 167 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 156 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 156 (by decide)
    have hact : actionA (codeMat 489) (codeMat 167) (codeMat 156) = codeMat 106 := by
      unfold actionA
      rw [step107o373s24_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 156 * (codeMat 167 : Mat3).transpose = codeMat 106
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 96 (by decide)
    have hact : actionA (codeMat 489) (codeMat 167) (codeMat 96) = codeMat 138 := by
      unfold actionA
      rw [step107o373s24_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 96 * (codeMat 167 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 136 ∈ o237W :=
      spanContainsCodeCore_implies_mem_spanCodes [266, 136, 96, 20, 1] 136 (by decide)
    have hact : actionA (codeMat 489) (codeMat 167) (codeMat 136) = codeMat 300 := by
      unfold actionA
      rw [step107o373s24_QtInv]
      show (codeMat 489 : Mat3).transpose * codeMat 136 * (codeMat 167 : Mat3).transpose = codeMat 300
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row24_qr : QuotientRankAtLeast step107o373ActualSource24 16 := by
  have hP : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 489) (codeMat 167) o237W) 16 :=
    @quotientRankAtLeast_action (codeMat 489) (codeMat 167) hP hQ o237W 16 step99_orbit237_lb16_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource24 16 :=
    quotientRankAtLeast_mono step107o373s24_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 25: row orbit 153, theorem source 153, type action
private theorem step107o373s25_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s25_source_le_transport :
    step107o373ActualSource25 ≤ actionW (codeMat 86) (codeMat 212) o153W := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 224, 288]
    (actionW (codeMat 86) (codeMat 212) o153W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 256 ∈ o153W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 256 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o153W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 96) = codeMat 12 := by
      unfold actionA
      rw [step107o373s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 96 * (codeMat 86 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 112 ∈ o153W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 10, 1] 112 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 112) = codeMat 20 := by
      unfold actionA
      rw [step107o373s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 112 * (codeMat 86 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 26 ∈ o153W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 26) = codeMat 224 := by
      unfold actionA
      rw [step107o373s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 26 * (codeMat 86 : Mat3).transpose = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o153W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 86) (codeMat 212) (codeMat 1) = codeMat 288 := by
      unfold actionA
      rw [step107o373s25_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row25_qr : QuotientRankAtLeast step107o373ActualSource25 15 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 212) o153W) 15 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 212) hP hQ o153W 15 step98_orbit153_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource25 15 :=
    quotientRankAtLeast_mono step107o373s25_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 26: row orbit 65, theorem source 65, type action
private theorem step107o373s26_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = (codeMat 331 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * (codeMat 331 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s26_source_le_transport :
    step107o373ActualSource26 ≤ actionW (codeMat 140) (codeMat 410) o65W := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 70, 166, 288]
    (actionW (codeMat 140) (codeMat 410) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step107o373s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 331 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 160) = codeMat 12 := by
      unfold actionA
      rw [step107o373s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 331 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 480 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 480 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 480) = codeMat 20 := by
      unfold actionA
      rw [step107o373s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 480 * (codeMat 331 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 26 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 26) = codeMat 70 := by
      unfold actionA
      rw [step107o373s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 26 * (codeMat 331 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 287 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 287 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 287) = codeMat 166 := by
      unfold actionA
      rw [step107o373s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 287 * (codeMat 331 : Mat3).transpose = codeMat 166
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 260) = codeMat 288 := by
      unfold actionA
      rw [step107o373s26_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 260 * (codeMat 331 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row26_qr : QuotientRankAtLeast step107o373ActualSource26 15 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 410) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 410) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource26 15 :=
    quotientRankAtLeast_mono step107o373s26_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 27: row orbit 69, theorem source 69, type action
private theorem step107o373s27_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s27_source_le_transport :
    step107o373ActualSource27 ≤ actionW (codeMat 204) (codeMat 270) o69W := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 34, 66, 128, 270]
    (actionW (codeMat 204) (codeMat 270) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 204) (codeMat 270) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step107o373s27_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 204) (codeMat 270) (codeMat 96) = codeMat 20 := by
      unfold actionA
      rw [step107o373s27_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 96 * (codeMat 298 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 352 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 352 (by decide)
    have hact : actionA (codeMat 204) (codeMat 270) (codeMat 352) = codeMat 34 := by
      unfold actionA
      rw [step107o373s27_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 352 * (codeMat 298 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 204) (codeMat 270) (codeMat 10) = codeMat 66 := by
      unfold actionA
      rw [step107o373s27_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 10 * (codeMat 298 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 204) (codeMat 270) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step107o373s27_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 181 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 181 (by decide)
    have hact : actionA (codeMat 204) (codeMat 270) (codeMat 181) = codeMat 270 := by
      unfold actionA
      rw [step107o373s27_QtInv]
      show (codeMat 204 : Mat3).transpose * codeMat 181 * (codeMat 298 : Mat3).transpose = codeMat 270
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row27_qr : QuotientRankAtLeast step107o373ActualSource27 15 := by
  have hP : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 204) (codeMat 270) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 204) (codeMat 270) hP hQ o69W 15 step99_orbit69_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource27 15 :=
    quotientRankAtLeast_mono step107o373s27_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 28: row orbit 65, theorem source 65, type action
private theorem step107o373s28_QtInv :
    (codeMat 247 : Mat3).transpose⁻¹ = (codeMat 379 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 247 : Mat3).transpose * (codeMat 379 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s28_source_le_transport :
    step107o373ActualSource28 ≤ actionW (codeMat 102) (codeMat 247) o65W := by
  apply step107o373_spanCodes_le_of_gens [1, 20, 32, 78, 142, 268]
    (actionW (codeMat 102) (codeMat 247) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 102) (codeMat 247) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step107o373s28_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 320 * (codeMat 379 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 255 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 102) (codeMat 247) (codeMat 255) = codeMat 20 := by
      unfold actionA
      rw [step107o373s28_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 255 * (codeMat 379 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 27 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 102) (codeMat 247) (codeMat 27) = codeMat 32 := by
      unfold actionA
      rw [step107o373s28_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 27 * (codeMat 379 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 261 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 261 (by decide)
    have hact : actionA (codeMat 102) (codeMat 247) (codeMat 261) = codeMat 78 := by
      unfold actionA
      rw [step107o373s28_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 261 * (codeMat 379 : Mat3).transpose = codeMat 78
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 277 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 277 (by decide)
    have hact : actionA (codeMat 102) (codeMat 247) (codeMat 277) = codeMat 142 := by
      unfold actionA
      rw [step107o373s28_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 277 * (codeMat 379 : Mat3).transpose = codeMat 142
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 245 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 102) (codeMat 247) (codeMat 245) = codeMat 268 := by
      unfold actionA
      rw [step107o373s28_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 245 * (codeMat 379 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row28_qr : QuotientRankAtLeast step107o373ActualSource28 15 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 247 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 247) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 247) hP hQ o65W 15 step99_orbit65_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource28 15 :=
    quotientRankAtLeast_mono step107o373s28_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 29: row orbit 55, theorem source 55, type action
private theorem step107o373s29_QtInv :
    (codeMat 267 : Mat3).transpose⁻¹ = (codeMat 282 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 267 : Mat3).transpose * (codeMat 282 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s29_source_le_transport :
    step107o373ActualSource29 ≤ actionW (codeMat 345) (codeMat 267) o55W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 20, 36, 196, 264]
    (actionW (codeMat 345) (codeMat 267) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 345) (codeMat 267) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step107o373s29_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 3 * (codeMat 282 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 345) (codeMat 267) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step107o373s29_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 1 * (codeMat 282 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 13 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 345) (codeMat 267) (codeMat 13) = codeMat 20 := by
      unfold actionA
      rw [step107o373s29_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 13 * (codeMat 282 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 345) (codeMat 267) (codeMat 32) = codeMat 36 := by
      unfold actionA
      rw [step107o373s29_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 32 * (codeMat 282 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 134 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 345) (codeMat 267) (codeMat 134) = codeMat 196 := by
      unfold actionA
      rw [step107o373s29_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 134 * (codeMat 282 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 287 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 287 (by decide)
    have hact : actionA (codeMat 345) (codeMat 267) (codeMat 287) = codeMat 264 := by
      unfold actionA
      rw [step107o373s29_QtInv]
      show (codeMat 345 : Mat3).transpose * codeMat 287 * (codeMat 282 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row29_qr : QuotientRankAtLeast step107o373ActualSource29 14 := by
  have hP : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 345) (codeMat 267) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 345) (codeMat 267) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource29 14 :=
    quotientRankAtLeast_mono step107o373s29_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 30: row orbit 55, theorem source 55, type transpose
private theorem step107o373s30_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s30_source_le_transport :
    step107o373ActualSource30 ≤ transposeW (actionW (codeMat 351) (codeMat 204) o55W) := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 38, 198, 262]
    (transposeW (actionW (codeMat 351) (codeMat 204) o55W))
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 351) (codeMat 204) (codeMat 438) = codeMat 1 := by
      unfold actionA
      rw [step107o373s30_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 438 * (codeMat 114 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 1 ∈ actionW (codeMat 351) (codeMat 204) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 1 : Mat3).transpose = codeMat 1 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h1
    have hw : codeMat 274 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 351) (codeMat 204) (codeMat 274) = codeMat 66 := by
      unfold actionA
      rw [step107o373s30_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 274 * (codeMat 114 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 66 ∈ actionW (codeMat 351) (codeMat 204) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 66 : Mat3).transpose = codeMat 12 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h2
    have hw : codeMat 306 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 306 (by decide)
    have hact : actionA (codeMat 351) (codeMat 204) (codeMat 306) = codeMat 80 := by
      unfold actionA
      rw [step107o373s30_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 306 * (codeMat 114 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 80 ∈ actionW (codeMat 351) (codeMat 204) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 80 : Mat3).transpose = codeMat 20 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h3
    have hw : codeMat 404 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 404 (by decide)
    have hact : actionA (codeMat 351) (codeMat 204) (codeMat 404) = codeMat 200 := by
      unfold actionA
      rw [step107o373s30_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 404 * (codeMat 114 : Mat3).transpose = codeMat 200
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 200 ∈ actionW (codeMat 351) (codeMat 204) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 200 : Mat3).transpose = codeMat 38 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h4
    have hw : codeMat 440 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 440 (by decide)
    have hact : actionA (codeMat 351) (codeMat 204) (codeMat 440) = codeMat 108 := by
      unfold actionA
      rw [step107o373s30_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 440 * (codeMat 114 : Mat3).transpose = codeMat 108
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 108 ∈ actionW (codeMat 351) (codeMat 204) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 108 : Mat3).transpose = codeMat 198 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans
  · subst h5
    have hw : codeMat 441 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 441 (by decide)
    have hact : actionA (codeMat 351) (codeMat 204) (codeMat 441) = codeMat 328 := by
      unfold actionA
      rw [step107o373s30_QtInv]
      show (codeMat 351 : Mat3).transpose * codeMat 441 * (codeMat 114 : Mat3).transpose = codeMat 328
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    have hmemAction : codeMat 328 ∈ actionW (codeMat 351) (codeMat 204) o55W :=
      step107o373_codeMat_mem_actionW_of_witness hw hact
    have htrans : (codeMat 328 : Mat3).transpose = codeMat 262 := by
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_transposeW_of_witness hmemAction htrans

theorem step107_o373_row30_qr : QuotientRankAtLeast step107o373ActualSource30 14 := by
  have hP : Invertible (codeMat 351 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 351) (codeMat 204) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 351) (codeMat 204) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hT : QuotientRankAtLeast (transposeW (actionW (codeMat 351) (codeMat 204) o55W)) 14 :=
    quotientRankAtLeast_transpose hAct
  have hMono : QuotientRankAtLeast step107o373ActualSource30 14 :=
    quotientRankAtLeast_mono step107o373s30_source_le_transport hT
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 31: row orbit 10, theorem source 10, type action
private theorem step107o373s31_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s31_source_le_transport :
    step107o373ActualSource31 ≤ actionW (codeMat 140) (codeMat 412) orbit10W := by
  apply step107o373_spanCodes_le_of_gens [1, 6, 10, 18, 64, 160, 288]
    (actionW (codeMat 140) (codeMat 412) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 412) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step107o373s31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 412) (codeMat 24) = codeMat 6 := by
      unfold actionA
      rw [step107o373s31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 111 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 176 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 176 (by decide)
    have hact : actionA (codeMat 140) (codeMat 412) (codeMat 176) = codeMat 10 := by
      unfold actionA
      rw [step107o373s31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 176 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 432 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 432 (by decide)
    have hact : actionA (codeMat 140) (codeMat 412) (codeMat 432) = codeMat 18 := by
      unfold actionA
      rw [step107o373s31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 432 * (codeMat 111 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 412) (codeMat 2) = codeMat 64 := by
      unfold actionA
      rw [step107o373s31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 111 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 326 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 326 (by decide)
    have hact : actionA (codeMat 140) (codeMat 412) (codeMat 326) = codeMat 160 := by
      unfold actionA
      rw [step107o373s31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 326 * (codeMat 111 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 140) (codeMat 412) (codeMat 325) = codeMat 288 := by
      unfold actionA
      rw [step107o373s31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 325 * (codeMat 111 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row31_qr : QuotientRankAtLeast step107o373ActualSource31 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 412) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 412) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource31 12 :=
    quotientRankAtLeast_mono step107o373s31_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 32: row orbit 10, theorem source 10, type action
private theorem step107o373s32_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s32_source_le_transport :
    step107o373ActualSource32 ≤ actionW (codeMat 140) (codeMat 281) orbit10W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 20, 32, 64, 128, 268]
    (actionW (codeMat 140) (codeMat 281) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step107o373s32_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step107o373s32_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 160) = codeMat 20 := by
      unfold actionA
      rw [step107o373s32_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 160 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step107o373s32_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 3) = codeMat 64 := by
      unfold actionA
      rw [step107o373s32_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step107o373s32_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 228 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 228 (by decide)
    have hact : actionA (codeMat 140) (codeMat 281) (codeMat 228) = codeMat 268 := by
      unfold actionA
      rw [step107o373s32_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 228 * (codeMat 281 : Mat3).transpose = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row32_qr : QuotientRankAtLeast step107o373ActualSource32 12 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 281) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 281) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource32 12 :=
    quotientRankAtLeast_mono step107o373s32_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 33: row orbit 10, theorem source 10, type action
private theorem step107o373s33_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s33_source_le_transport :
    step107o373ActualSource33 ≤ actionW (codeMat 270) (codeMat 281) orbit10W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 20, 44, 72, 132, 256]
    (actionW (codeMat 270) (codeMat 281) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 270) (codeMat 281) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step107o373s33_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 24 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 270) (codeMat 281) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step107o373s33_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 162 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 162 (by decide)
    have hact : actionA (codeMat 270) (codeMat 281) (codeMat 162) = codeMat 20 := by
      unfold actionA
      rw [step107o373s33_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 162 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 487 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 487 (by decide)
    have hact : actionA (codeMat 270) (codeMat 281) (codeMat 487) = codeMat 44 := by
      unfold actionA
      rw [step107o373s33_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 487 * (codeMat 281 : Mat3).transpose = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 270) (codeMat 281) (codeMat 3) = codeMat 72 := by
      unfold actionA
      rw [step107o373s33_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 270) (codeMat 281) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step107o373s33_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 160 * (codeMat 281 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 270) (codeMat 281) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step107o373s33_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row33_qr : QuotientRankAtLeast step107o373ActualSource33 12 := by
  have hP : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 270) (codeMat 281) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 270) (codeMat 281) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource33 12 :=
    quotientRankAtLeast_mono step107o373s33_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 34: row orbit 14, theorem source 14, type action
private theorem step107o373s34_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = (codeMat 401 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * (codeMat 401 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s34_source_le_transport :
    step107o373ActualSource34 ≤ actionW (codeMat 249) (codeMat 401) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 6, 18, 34, 72, 138, 264]
    (actionW (codeMat 249) (codeMat 401) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 249) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s34_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 1 * (codeMat 401 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 249) (codeMat 401) (codeMat 2) = codeMat 6 := by
      unfold actionA
      rw [step107o373s34_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 2 * (codeMat 401 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 249) (codeMat 401) (codeMat 384) = codeMat 18 := by
      unfold actionA
      rw [step107o373s34_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 384 * (codeMat 401 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 258 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 258 (by decide)
    have hact : actionA (codeMat 249) (codeMat 401) (codeMat 258) = codeMat 34 := by
      unfold actionA
      rw [step107o373s34_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 258 * (codeMat 401 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 249) (codeMat 401) (codeMat 9) = codeMat 72 := by
      unfold actionA
      rw [step107o373s34_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 9 * (codeMat 401 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 503 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 503 (by decide)
    have hact : actionA (codeMat 249) (codeMat 401) (codeMat 503) = codeMat 138 := by
      unfold actionA
      rw [step107o373s34_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 503 * (codeMat 401 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 353 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 353 (by decide)
    have hact : actionA (codeMat 249) (codeMat 401) (codeMat 353) = codeMat 264 := by
      unfold actionA
      rw [step107o373s34_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 353 * (codeMat 401 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row34_qr : QuotientRankAtLeast step107o373ActualSource34 12 := by
  have hP : Invertible (codeMat 249 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 249) (codeMat 401) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 249) (codeMat 401) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource34 12 :=
    quotientRankAtLeast_mono step107o373s34_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 35: row orbit 14, theorem source 14, type action
private theorem step107o373s35_QtInv :
    (codeMat 442 : Mat3).transpose⁻¹ = (codeMat 334 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 442 : Mat3).transpose * (codeMat 334 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s35_source_le_transport :
    step107o373ActualSource35 ≤ actionW (codeMat 103) (codeMat 442) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 16, 34, 72, 138, 266]
    (actionW (codeMat 103) (codeMat 442) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 103) (codeMat 442) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s35_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 128 * (codeMat 334 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 103) (codeMat 442) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step107o373s35_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 384 * (codeMat 334 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 103) (codeMat 442) (codeMat 511) = codeMat 16 := by
      unfold actionA
      rw [step107o373s35_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 511 * (codeMat 334 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 103) (codeMat 442) (codeMat 118) = codeMat 34 := by
      unfold actionA
      rw [step107o373s35_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 118 * (codeMat 334 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 103) (codeMat 442) (codeMat 130) = codeMat 72 := by
      unfold actionA
      rw [step107o373s35_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 130 * (codeMat 334 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 362 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 362 (by decide)
    have hact : actionA (codeMat 103) (codeMat 442) (codeMat 362) = codeMat 138 := by
      unfold actionA
      rw [step107o373s35_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 362 * (codeMat 334 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 354 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 354 (by decide)
    have hact : actionA (codeMat 103) (codeMat 442) (codeMat 354) = codeMat 266 := by
      unfold actionA
      rw [step107o373s35_QtInv]
      show (codeMat 103 : Mat3).transpose * codeMat 354 * (codeMat 334 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row35_qr : QuotientRankAtLeast step107o373ActualSource35 12 := by
  have hP : Invertible (codeMat 103 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 442 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 103) (codeMat 442) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 103) (codeMat 442) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource35 12 :=
    quotientRankAtLeast_mono step107o373s35_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 36: row orbit 14, theorem source 14, type action
private theorem step107o373s36_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s36_source_le_transport :
    step107o373ActualSource36 ≤ actionW (codeMat 473) (codeMat 273) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 8, 20, 100, 132, 292]
    (actionW (codeMat 473) (codeMat 273) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s36_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step107o373s36_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 9) = codeMat 8 := by
      unfold actionA
      rw [step107o373s36_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 9 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 22 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 22 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 22) = codeMat 20 := by
      unfold actionA
      rw [step107o373s36_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 22 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 104 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 104 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 104) = codeMat 100 := by
      unfold actionA
      rw [step107o373s36_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 104 * (codeMat 273 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 148) = codeMat 132 := by
      unfold actionA
      rw [step107o373s36_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 148 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 473) (codeMat 273) (codeMat 256) = codeMat 292 := by
      unfold actionA
      rw [step107o373s36_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row36_qr : QuotientRankAtLeast step107o373ActualSource36 12 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 273) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 273) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource36 12 :=
    quotientRankAtLeast_mono step107o373s36_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 37: row orbit 3, theorem source 3, type action
private theorem step107o373s37_QtInv :
    (codeMat 116 : Mat3).transpose⁻¹ = (codeMat 92 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 116 : Mat3).transpose * (codeMat 92 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s37_source_le_transport :
    step107o373ActualSource37 ≤ actionW (codeMat 84) (codeMat 116) flatW_3 := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 8, 20, 36, 68, 128, 256]
    (actionW (codeMat 84) (codeMat 116) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 92 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 92 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 92 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 208 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 208 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 208) = codeMat 20 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 208 * (codeMat 92 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 216 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 216 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 216) = codeMat 36 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 216 * (codeMat 92 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 196 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 196 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 196) = codeMat 68 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 196 * (codeMat 92 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 92 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 3 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 116) (codeMat 3) = codeMat 256 := by
      unfold actionA
      rw [step107o373s37_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 92 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row37_qr : QuotientRankAtLeast step107o373ActualSource37 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 116) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 116) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step107o373ActualSource37 9 :=
    quotientRankAtLeast_mono step107o373s37_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 38: row orbit 69, theorem source 69, type action
private theorem step107o373s38_QtInv :
    (codeMat 242 : Mat3).transpose⁻¹ = (codeMat 205 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 242 : Mat3).transpose * (codeMat 205 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s38_source_le_transport :
    step107o373ActualSource38 ≤ actionW (codeMat 116) (codeMat 242) o69W := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 66, 162, 288]
    (actionW (codeMat 116) (codeMat 242) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 116) (codeMat 242) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s38_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 256 * (codeMat 205 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 164 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 116) (codeMat 242) (codeMat 164) = codeMat 12 := by
      unfold actionA
      rw [step107o373s38_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 164 * (codeMat 205 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 191 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 116) (codeMat 242) (codeMat 191) = codeMat 20 := by
      unfold actionA
      rw [step107o373s38_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 191 * (codeMat 205 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 452 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 116) (codeMat 242) (codeMat 452) = codeMat 66 := by
      unfold actionA
      rw [step107o373s38_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 452 * (codeMat 205 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 469 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 469 (by decide)
    have hact : actionA (codeMat 116) (codeMat 242) (codeMat 469) = codeMat 162 := by
      unfold actionA
      rw [step107o373s38_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 469 * (codeMat 205 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 116) (codeMat 242) (codeMat 16) = codeMat 288 := by
      unfold actionA
      rw [step107o373s38_QtInv]
      show (codeMat 116 : Mat3).transpose * codeMat 16 * (codeMat 205 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row38_qr : QuotientRankAtLeast step107o373ActualSource38 15 := by
  have hP : Invertible (codeMat 116 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 242 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 116) (codeMat 242) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 116) (codeMat 242) hP hQ o69W 15 step99_orbit69_lb15_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource38 15 :=
    quotientRankAtLeast_mono step107o373s38_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 39: row orbit 55, theorem source 55, type action
private theorem step107o373s39_QtInv :
    (codeMat 299 : Mat3).transpose⁻¹ = (codeMat 318 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 299 : Mat3).transpose * (codeMat 318 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s39_source_le_transport :
    step107o373ActualSource39 ≤ actionW (codeMat 473) (codeMat 299) o55W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 20, 40, 200, 260]
    (actionW (codeMat 473) (codeMat 299) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 473) (codeMat 299) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step107o373s39_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 3 * (codeMat 318 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 299) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [step107o373s39_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 318 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 15 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 15 (by decide)
    have hact : actionA (codeMat 473) (codeMat 299) (codeMat 15) = codeMat 20 := by
      unfold actionA
      rw [step107o373s39_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 15 * (codeMat 318 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 473) (codeMat 299) (codeMat 45) = codeMat 40 := by
      unfold actionA
      rw [step107o373s39_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 45 * (codeMat 318 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 139 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 139 (by decide)
    have hact : actionA (codeMat 473) (codeMat 299) (codeMat 139) = codeMat 200 := by
      unfold actionA
      rw [step107o373s39_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 139 * (codeMat 318 : Mat3).transpose = codeMat 200
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 473) (codeMat 299) (codeMat 438) = codeMat 260 := by
      unfold actionA
      rw [step107o373s39_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 438 * (codeMat 318 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row39_qr : QuotientRankAtLeast step107o373ActualSource39 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 299 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 299) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 299) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource39 14 :=
    quotientRankAtLeast_mono step107o373s39_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 40: row orbit 14, theorem source 14, type action
private theorem step107o373s40_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s40_source_le_transport :
    step107o373ActualSource40 ≤ actionW (codeMat 93) (codeMat 110) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 6, 18, 40, 74, 130, 258]
    (actionW (codeMat 93) (codeMat 110) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 93) (codeMat 110) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step107o373s40_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 384 * (codeMat 444 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 93) (codeMat 110) (codeMat 128) = codeMat 6 := by
      unfold actionA
      rw [step107o373s40_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 128 * (codeMat 444 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 93) (codeMat 110) (codeMat 8) = codeMat 18 := by
      unfold actionA
      rw [step107o373s40_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 8 * (codeMat 444 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 93) (codeMat 110) (codeMat 360) = codeMat 40 := by
      unfold actionA
      rw [step107o373s40_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 360 * (codeMat 444 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 93) (codeMat 110) (codeMat 118) = codeMat 74 := by
      unfold actionA
      rw [step107o373s40_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 118 * (codeMat 444 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 93) (codeMat 110) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [step107o373s40_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 1 * (codeMat 444 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 131 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 131 (by decide)
    have hact : actionA (codeMat 93) (codeMat 110) (codeMat 131) = codeMat 258 := by
      unfold actionA
      rw [step107o373s40_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 131 * (codeMat 444 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row40_qr : QuotientRankAtLeast step107o373ActualSource40 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 110) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 110) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource40 12 :=
    quotientRankAtLeast_mono step107o373s40_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 41: row orbit 14, theorem source 14, type action
private theorem step107o373s41_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s41_source_le_transport :
    step107o373ActualSource41 ≤ actionW (codeMat 111) (codeMat 266) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 16, 42, 72, 130, 258]
    (actionW (codeMat 111) (codeMat 266) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 111) (codeMat 266) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s41_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 111) (codeMat 266) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step107o373s41_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 111) (codeMat 266) (codeMat 9) = codeMat 16 := by
      unfold actionA
      rw [step107o373s41_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 9 * (codeMat 266 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 118 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 118 (by decide)
    have hact : actionA (codeMat 111) (codeMat 266) (codeMat 118) = codeMat 42 := by
      unfold actionA
      rw [step107o373s41_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 118 * (codeMat 266 : Mat3).transpose = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 111) (codeMat 266) (codeMat 130) = codeMat 72 := by
      unfold actionA
      rw [step107o373s41_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 130 * (codeMat 266 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 111) (codeMat 266) (codeMat 8) = codeMat 130 := by
      unfold actionA
      rw [step107o373s41_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 111) (codeMat 266) (codeMat 352) = codeMat 258 := by
      unfold actionA
      rw [step107o373s41_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 352 * (codeMat 266 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row41_qr : QuotientRankAtLeast step107o373ActualSource41 12 := by
  have hP : Invertible (codeMat 111 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 111) (codeMat 266) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 111) (codeMat 266) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource41 12 :=
    quotientRankAtLeast_mono step107o373s41_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 42: row orbit 14, theorem source 14, type action
private theorem step107o373s42_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s42_source_le_transport :
    step107o373ActualSource42 ≤ actionW (codeMat 85) (codeMat 172) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 20, 40, 64, 136, 260]
    (actionW (codeMat 85) (codeMat 172) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 85) (codeMat 172) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s42_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 128 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 172) (codeMat 256) = codeMat 2 := by
      unfold actionA
      rw [step107o373s42_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 99 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 224 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 224 (by decide)
    have hact : actionA (codeMat 85) (codeMat 172) (codeMat 224) = codeMat 20 := by
      unfold actionA
      rw [step107o373s42_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 224 * (codeMat 99 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 172) (codeMat 8) = codeMat 40 := by
      unfold actionA
      rw [step107o373s42_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 99 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 85) (codeMat 172) (codeMat 130) = codeMat 64 := by
      unfold actionA
      rw [step107o373s42_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 130 * (codeMat 99 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 276 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 276 (by decide)
    have hact : actionA (codeMat 85) (codeMat 172) (codeMat 276) = codeMat 136 := by
      unfold actionA
      rw [step107o373s42_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 276 * (codeMat 99 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 85) (codeMat 172) (codeMat 3) = codeMat 260 := by
      unfold actionA
      rw [step107o373s42_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 3 * (codeMat 99 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row42_qr : QuotientRankAtLeast step107o373ActualSource42 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 172) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 172) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource42 12 :=
    quotientRankAtLeast_mono step107o373s42_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 43: row orbit 14, theorem source 14, type action
private theorem step107o373s43_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s43_source_le_transport :
    step107o373ActualSource43 ≤ actionW (codeMat 337) (codeMat 277) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 8, 20, 96, 128, 292]
    (actionW (codeMat 337) (codeMat 277) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s43_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step107o373s43_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step107o373s43_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 8 * (codeMat 277 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 21 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 21 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 21) = codeMat 20 := by
      unfold actionA
      rw [step107o373s43_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 21 * (codeMat 277 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 105 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 105 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 105) = codeMat 96 := by
      unfold actionA
      rw [step107o373s43_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 105 * (codeMat 277 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 130 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 130 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 130) = codeMat 128 := by
      unfold actionA
      rw [step107o373s43_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 130 * (codeMat 277 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 337) (codeMat 277) (codeMat 360) = codeMat 292 := by
      unfold actionA
      rw [step107o373s43_QtInv]
      show (codeMat 337 : Mat3).transpose * codeMat 360 * (codeMat 277 : Mat3).transpose = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row43_qr : QuotientRankAtLeast step107o373ActualSource43 12 := by
  have hP : Invertible (codeMat 337 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 337) (codeMat 277) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 337) (codeMat 277) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource43 12 :=
    quotientRankAtLeast_mono step107o373s43_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 44: row orbit 11, theorem source 11, type action
private theorem step107o373s44_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s44_source_le_transport :
    step107o373ActualSource44 ≤ actionW (codeMat 102) (codeMat 172) orbit11W := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 36, 68, 128, 260]
    (actionW (codeMat 102) (codeMat 172) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step107o373s44_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 128 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 210 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 210 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 210) = codeMat 12 := by
      unfold actionA
      rw [step107o373s44_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 210 * (codeMat 99 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 228 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 228 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 228) = codeMat 20 := by
      unfold actionA
      rw [step107o373s44_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 228 * (codeMat 99 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 219 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 219 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 219) = codeMat 36 := by
      unfold actionA
      rw [step107o373s44_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 219 * (codeMat 99 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 208 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 208 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 208) = codeMat 68 := by
      unfold actionA
      rw [step107o373s44_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 208 * (codeMat 99 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 32) = codeMat 128 := by
      unfold actionA
      rw [step107o373s44_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 32 * (codeMat 99 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 216 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 216 (by decide)
    have hact : actionA (codeMat 102) (codeMat 172) (codeMat 216) = codeMat 260 := by
      unfold actionA
      rw [step107o373s44_QtInv]
      show (codeMat 102 : Mat3).transpose * codeMat 216 * (codeMat 99 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row44_qr : QuotientRankAtLeast step107o373ActualSource44 12 := by
  have hP : Invertible (codeMat 102 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 102) (codeMat 172) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 102) (codeMat 172) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource44 12 :=
    quotientRankAtLeast_mono step107o373s44_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 45: row orbit 14, theorem source 14, type action
private theorem step107o373s45_QtInv :
    (codeMat 354 : Mat3).transpose⁻¹ = (codeMat 142 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 354 : Mat3).transpose * (codeMat 142 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s45_source_le_transport :
    step107o373ActualSource45 ≤ actionW (codeMat 85) (codeMat 354) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 10, 16, 98, 130, 290]
    (actionW (codeMat 85) (codeMat 354) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 85) (codeMat 354) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s45_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 256 * (codeMat 142 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 85) (codeMat 354) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step107o373s45_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 384 * (codeMat 142 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 85) (codeMat 354) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step107o373s45_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 96 * (codeMat 142 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 85) (codeMat 354) (codeMat 8) = codeMat 16 := by
      unfold actionA
      rw [step107o373s45_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 8 * (codeMat 142 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 372 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 372 (by decide)
    have hact : actionA (codeMat 85) (codeMat 354) (codeMat 372) = codeMat 98 := by
      unfold actionA
      rw [step107o373s45_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 372 * (codeMat 142 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 85) (codeMat 354) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [step107o373s45_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 1 * (codeMat 142 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 502 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 502 (by decide)
    have hact : actionA (codeMat 85) (codeMat 354) (codeMat 502) = codeMat 290 := by
      unfold actionA
      rw [step107o373s45_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 502 * (codeMat 142 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row45_qr : QuotientRankAtLeast step107o373ActualSource45 12 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 354 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 354) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 354) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource45 12 :=
    quotientRankAtLeast_mono step107o373s45_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 46: row orbit 14, theorem source 14, type action
private theorem step107o373s46_QtInv :
    (codeMat 95 : Mat3).transpose⁻¹ = (codeMat 244 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 95 : Mat3).transpose * (codeMat 244 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s46_source_le_transport :
    step107o373ActualSource46 ≤ actionW (codeMat 181) (codeMat 95) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 36, 70, 130, 260]
    (actionW (codeMat 181) (codeMat 95) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 511 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 511 (by decide)
    have hact : actionA (codeMat 181) (codeMat 95) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step107o373s46_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 511 * (codeMat 244 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 393 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 393 (by decide)
    have hact : actionA (codeMat 181) (codeMat 95) (codeMat 393) = codeMat 12 := by
      unfold actionA
      rw [step107o373s46_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 393 * (codeMat 244 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 137 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 137 (by decide)
    have hact : actionA (codeMat 181) (codeMat 95) (codeMat 137) = codeMat 20 := by
      unfold actionA
      rw [step107o373s46_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 137 * (codeMat 244 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 9 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 9 (by decide)
    have hact : actionA (codeMat 181) (codeMat 95) (codeMat 9) = codeMat 36 := by
      unfold actionA
      rw [step107o373s46_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 9 * (codeMat 244 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 362 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 362 (by decide)
    have hact : actionA (codeMat 181) (codeMat 95) (codeMat 362) = codeMat 70 := by
      unfold actionA
      rw [step107o373s46_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 362 * (codeMat 244 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 181) (codeMat 95) (codeMat 3) = codeMat 130 := by
      unfold actionA
      rw [step107o373s46_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 3 * (codeMat 244 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 181) (codeMat 95) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [step107o373s46_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 1 * (codeMat 244 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row46_qr : QuotientRankAtLeast step107o373ActualSource46 12 := by
  have hP : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 181) (codeMat 95) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 181) (codeMat 95) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource46 12 :=
    quotientRankAtLeast_mono step107o373s46_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 47: row orbit 14, theorem source 14, type action
private theorem step107o373s47_QtInv :
    (codeMat 157 : Mat3).transpose⁻¹ = (codeMat 486 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 157 : Mat3).transpose * (codeMat 486 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s47_source_le_transport :
    step107o373ActualSource47 ≤ actionW (codeMat 161) (codeMat 157) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 16, 40, 66, 138, 256]
    (actionW (codeMat 161) (codeMat 157) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 161) (codeMat 157) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step107o373s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 3 * (codeMat 486 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 157) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step107o373s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 486 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 161) (codeMat 157) (codeMat 384) = codeMat 16 := by
      unfold actionA
      rw [step107o373s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 384 * (codeMat 486 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 157) (codeMat 128) = codeMat 40 := by
      unfold actionA
      rw [step107o373s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 486 : Mat3).transpose = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 30 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 30 (by decide)
    have hact : actionA (codeMat 161) (codeMat 157) (codeMat 30) = codeMat 66 := by
      unfold actionA
      rw [step107o373s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 30 * (codeMat 486 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 246 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 246 (by decide)
    have hact : actionA (codeMat 161) (codeMat 157) (codeMat 246) = codeMat 138 := by
      unfold actionA
      rw [step107o373s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 246 * (codeMat 486 : Mat3).transpose = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 157) (codeMat 8) = codeMat 256 := by
      unfold actionA
      rw [step107o373s47_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 486 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row47_qr : QuotientRankAtLeast step107o373ActualSource47 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 157 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 157) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 157) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource47 12 :=
    quotientRankAtLeast_mono step107o373s47_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 48: row orbit 11, theorem source 11, type action
private theorem step107o373s48_QtInv :
    (codeMat 253 : Mat3).transpose⁻¹ = (codeMat 415 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 253 : Mat3).transpose * (codeMat 415 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s48_source_le_transport :
    step107o373ActualSource48 ≤ actionW (codeMat 275) (codeMat 253) orbit11W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 12, 20, 36, 196, 260]
    (actionW (codeMat 275) (codeMat 253) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 63 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 63 (by decide)
    have hact : actionA (codeMat 275) (codeMat 253) (codeMat 63) = codeMat 1 := by
      unfold actionA
      rw [step107o373s48_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 63 * (codeMat 415 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 54 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 54 (by decide)
    have hact : actionA (codeMat 275) (codeMat 253) (codeMat 54) = codeMat 2 := by
      unfold actionA
      rw [step107o373s48_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 54 * (codeMat 415 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 35 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 35 (by decide)
    have hact : actionA (codeMat 275) (codeMat 253) (codeMat 35) = codeMat 12 := by
      unfold actionA
      rw [step107o373s48_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 35 * (codeMat 415 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 43 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 43 (by decide)
    have hact : actionA (codeMat 275) (codeMat 253) (codeMat 43) = codeMat 20 := by
      unfold actionA
      rw [step107o373s48_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 43 * (codeMat 415 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 275) (codeMat 253) (codeMat 3) = codeMat 36 := by
      unfold actionA
      rw [step107o373s48_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 3 * (codeMat 415 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 91 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 91 (by decide)
    have hact : actionA (codeMat 275) (codeMat 253) (codeMat 91) = codeMat 196 := by
      unfold actionA
      rw [step107o373s48_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 91 * (codeMat 415 : Mat3).transpose = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 219 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 219 (by decide)
    have hact : actionA (codeMat 275) (codeMat 253) (codeMat 219) = codeMat 260 := by
      unfold actionA
      rw [step107o373s48_QtInv]
      show (codeMat 275 : Mat3).transpose * codeMat 219 * (codeMat 415 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row48_qr : QuotientRankAtLeast step107o373ActualSource48 12 := by
  have hP : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 253 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 275) (codeMat 253) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 275) (codeMat 253) hP hQ orbit11W 12 orbit11_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource48 12 :=
    quotientRankAtLeast_mono step107o373s48_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 49: row orbit 10, theorem source 10, type action
private theorem step107o373s49_QtInv :
    (codeMat 242 : Mat3).transpose⁻¹ = (codeMat 205 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 242 : Mat3).transpose * (codeMat 205 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s49_source_le_transport :
    step107o373ActualSource49 ≤ actionW (codeMat 84) (codeMat 242) orbit10W := by
  apply step107o373_spanCodes_le_of_gens [1, 12, 20, 32, 70, 134, 256]
    (actionW (codeMat 84) (codeMat 242) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 242) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s49_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 205 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 242) (codeMat 160) = codeMat 12 := by
      unfold actionA
      rw [step107o373s49_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 205 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 184 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 184 (by decide)
    have hact : actionA (codeMat 84) (codeMat 242) (codeMat 184) = codeMat 20 := by
      unfold actionA
      rw [step107o373s49_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 184 * (codeMat 205 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 242) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step107o373s49_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 205 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 324 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 324 (by decide)
    have hact : actionA (codeMat 84) (codeMat 242) (codeMat 324) = codeMat 70 := by
      unfold actionA
      rw [step107o373s49_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 205 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 327 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 327 (by decide)
    have hact : actionA (codeMat 84) (codeMat 242) (codeMat 327) = codeMat 134 := by
      unfold actionA
      rw [step107o373s49_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 327 * (codeMat 205 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 242) (codeMat 2) = codeMat 256 := by
      unfold actionA
      rw [step107o373s49_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 205 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row49_qr : QuotientRankAtLeast step107o373ActualSource49 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 242 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 242) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 242) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource49 12 :=
    quotientRankAtLeast_mono step107o373s49_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 50: row orbit 10, theorem source 10, type action
private theorem step107o373s50_QtInv :
    (codeMat 415 : Mat3).transpose⁻¹ = (codeMat 253 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 415 : Mat3).transpose * (codeMat 253 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s50_source_le_transport :
    step107o373ActualSource50 ≤ actionW (codeMat 270) (codeMat 415) orbit10W := by
  apply step107o373_spanCodes_le_of_gens [1, 6, 18, 32, 72, 136, 266]
    (actionW (codeMat 270) (codeMat 415) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 24 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 24 (by decide)
    have hact : actionA (codeMat 270) (codeMat 415) (codeMat 24) = codeMat 1 := by
      unfold actionA
      rw [step107o373s50_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 24 * (codeMat 253 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 270) (codeMat 415) (codeMat 16) = codeMat 6 := by
      unfold actionA
      rw [step107o373s50_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 16 * (codeMat 253 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 511 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 511 (by decide)
    have hact : actionA (codeMat 270) (codeMat 415) (codeMat 511) = codeMat 18 := by
      unfold actionA
      rw [step107o373s50_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 511 * (codeMat 253 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 325 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 325 (by decide)
    have hact : actionA (codeMat 270) (codeMat 415) (codeMat 325) = codeMat 32 := by
      unfold actionA
      rw [step107o373s50_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 325 * (codeMat 253 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 3 (by decide)
    have hact : actionA (codeMat 270) (codeMat 415) (codeMat 3) = codeMat 72 := by
      unfold actionA
      rw [step107o373s50_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 3 * (codeMat 253 : Mat3).transpose = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 259 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 259 (by decide)
    have hact : actionA (codeMat 270) (codeMat 415) (codeMat 259) = codeMat 136 := by
      unfold actionA
      rw [step107o373s50_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 259 * (codeMat 253 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 443 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 443 (by decide)
    have hact : actionA (codeMat 270) (codeMat 415) (codeMat 443) = codeMat 266 := by
      unfold actionA
      rw [step107o373s50_QtInv]
      show (codeMat 270 : Mat3).transpose * codeMat 443 * (codeMat 253 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row50_qr : QuotientRankAtLeast step107o373ActualSource50 12 := by
  have hP : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 415 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 270) (codeMat 415) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 270) (codeMat 415) hP hQ orbit10W 12 orbit10_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource50 12 :=
    quotientRankAtLeast_mono step107o373s50_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 51: row orbit 3, theorem source 3, type action
private theorem step107o373s51_QtInv :
    (codeMat 468 : Mat3).transpose⁻¹ = (codeMat 87 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 468 : Mat3).transpose * (codeMat 87 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s51_source_le_transport :
    step107o373ActualSource51 ≤ actionW (codeMat 84) (codeMat 468) flatW_3 := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 8, 20, 32, 68, 132, 260]
    (actionW (codeMat 84) (codeMat 468) flatW_3)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · subst h0
    have hw : codeMat 256 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 87 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 384) = codeMat 2 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 384 * (codeMat 87 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 32) = codeMat 8 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 32 * (codeMat 87 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 368 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 368 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 368) = codeMat 20 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 368 * (codeMat 87 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 40 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 40) = codeMat 32 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 40 * (codeMat 87 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 324 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 324 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 324) = codeMat 68 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 324 * (codeMat 87 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 326 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 326 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 326) = codeMat 132 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 326 * (codeMat 87 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h7
    have hw : codeMat 325 ∈ flatW_3 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] 325 (by decide)
    have hact : actionA (codeMat 84) (codeMat 468) (codeMat 325) = codeMat 260 := by
      unfold actionA
      rw [step107o373s51_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 325 * (codeMat 87 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row51_qr : QuotientRankAtLeast step107o373ActualSource51 9 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 468 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 468) flatW_3) 9 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 468) hP hQ flatW_3 9 flatSeed_3
  have hMono : QuotientRankAtLeast step107o373ActualSource51 9 :=
    quotientRankAtLeast_mono step107o373s51_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 52: row orbit 55, theorem source 55, type action
private theorem step107o373s52_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = (codeMat 165 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * (codeMat 165 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s52_source_le_transport :
    step107o373ActualSource52 ≤ actionW (codeMat 473) (codeMat 163) o55W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 10, 16, 224, 290]
    (actionW (codeMat 473) (codeMat 163) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 1 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 473) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step107o373s52_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 1 * (codeMat 165 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 473) (codeMat 163) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step107o373s52_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 2 * (codeMat 165 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 12 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 12 (by decide)
    have hact : actionA (codeMat 473) (codeMat 163) (codeMat 12) = codeMat 10 := by
      unfold actionA
      rw [step107o373s52_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 12 * (codeMat 165 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 45 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 473) (codeMat 163) (codeMat 45) = codeMat 16 := by
      unfold actionA
      rw [step107o373s52_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 45 * (codeMat 165 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 306 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 306 (by decide)
    have hact : actionA (codeMat 473) (codeMat 163) (codeMat 306) = codeMat 224 := by
      unfold actionA
      rw [step107o373s52_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 306 * (codeMat 165 : Mat3).transpose = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 135 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 135 (by decide)
    have hact : actionA (codeMat 473) (codeMat 163) (codeMat 135) = codeMat 290 := by
      unfold actionA
      rw [step107o373s52_QtInv]
      show (codeMat 473 : Mat3).transpose * codeMat 135 * (codeMat 165 : Mat3).transpose = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row52_qr : QuotientRankAtLeast step107o373ActualSource52 14 := by
  have hP : Invertible (codeMat 473 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 473) (codeMat 163) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 473) (codeMat 163) hP hQ o55W 14 step99_orbit55_lb14_unconditional
  have hMono : QuotientRankAtLeast step107o373ActualSource52 14 :=
    quotientRankAtLeast_mono step107o373s52_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 53: row orbit 14, theorem source 14, type action
private theorem step107o373s53_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s53_source_le_transport :
    step107o373ActualSource53 ≤ actionW (codeMat 177) (codeMat 156) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 8, 16, 66, 162, 288]
    (actionW (codeMat 177) (codeMat 156) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 156) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step107o373s53_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 102 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 156) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [step107o373s53_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * (codeMat 102 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 177) (codeMat 156) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [step107o373s53_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 128 * (codeMat 102 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 177) (codeMat 156) (codeMat 384) = codeMat 16 := by
      unfold actionA
      rw [step107o373s53_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 384 * (codeMat 102 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 150 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 150 (by decide)
    have hact : actionA (codeMat 177) (codeMat 156) (codeMat 150) = codeMat 66 := by
      unfold actionA
      rw [step107o373s53_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 150 * (codeMat 102 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 502 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 502 (by decide)
    have hact : actionA (codeMat 177) (codeMat 156) (codeMat 502) = codeMat 162 := by
      unfold actionA
      rw [step107o373s53_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 502 * (codeMat 102 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 177) (codeMat 156) (codeMat 8) = codeMat 288 := by
      unfold actionA
      rw [step107o373s53_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 8 * (codeMat 102 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row53_qr : QuotientRankAtLeast step107o373ActualSource53 12 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 156) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 156) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource53 12 :=
    quotientRankAtLeast_mono step107o373s53_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 54: row orbit 14, theorem source 14, type action
private theorem step107o373s54_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s54_source_le_transport :
    step107o373ActualSource54 ≤ actionW (codeMat 106) (codeMat 98) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 16, 32, 66, 130, 264]
    (actionW (codeMat 106) (codeMat 98) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step107o373s54_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 128) = codeMat 4 := by
      unfold actionA
      rw [step107o373s54_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 128 * (codeMat 140 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 1 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step107o373s54_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [step107o373s54_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 352 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 352 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 352) = codeMat 66 := by
      unfold actionA
      rw [step107o373s54_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 352 * (codeMat 140 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 8) = codeMat 130 := by
      unfold actionA
      rw [step107o373s54_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 106) (codeMat 98) (codeMat 148) = codeMat 264 := by
      unfold actionA
      rw [step107o373s54_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 148 * (codeMat 140 : Mat3).transpose = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row54_qr : QuotientRankAtLeast step107o373ActualSource54 12 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 98) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 98) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource54 12 :=
    quotientRankAtLeast_mono step107o373s54_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 55: row orbit 14, theorem source 14, type action
private theorem step107o373s55_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s55_source_le_transport :
    step107o373ActualSource55 ≤ actionW (codeMat 401) (codeMat 281) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 2, 12, 20, 100, 132, 288]
    (actionW (codeMat 401) (codeMat 281) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [step107o373s55_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step107o373s55_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 28 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 28 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 28) = codeMat 12 := by
      unfold actionA
      rw [step107o373s55_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 28 * (codeMat 281 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [step107o373s55_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 20 * (codeMat 281 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 252 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 252 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 252) = codeMat 100 := by
      unfold actionA
      rw [step107o373s55_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 252 * (codeMat 281 : Mat3).transpose = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 148 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 148 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 148) = codeMat 132 := by
      unfold actionA
      rw [step107o373s55_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 148 * (codeMat 281 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 401) (codeMat 281) (codeMat 256) = codeMat 288 := by
      unfold actionA
      rw [step107o373s55_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row55_qr : QuotientRankAtLeast step107o373ActualSource55 12 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 281) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 281) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource55 12 :=
    quotientRankAtLeast_mono step107o373s55_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

-- Dispatch for source 56: row orbit 14, theorem source 14, type action
private theorem step107o373s56_QtInv :
    (codeMat 458 : Mat3).transpose⁻¹ = (codeMat 458 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 458 : Mat3).transpose * (codeMat 458 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step107o373s56_source_le_transport :
    step107o373ActualSource56 ≤ actionW (codeMat 93) (codeMat 458) orbit14W := by
  apply step107o373_spanCodes_le_of_gens [1, 4, 16, 34, 74, 136, 266]
    (actionW (codeMat 93) (codeMat 458) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 384 (by decide)
    have hact : actionA (codeMat 93) (codeMat 458) (codeMat 384) = codeMat 1 := by
      unfold actionA
      rw [step107o373s56_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 384 * (codeMat 458 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 458) (codeMat 256) = codeMat 4 := by
      unfold actionA
      rw [step107o373s56_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 458 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 360 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 360 (by decide)
    have hact : actionA (codeMat 93) (codeMat 458) (codeMat 360) = codeMat 16 := by
      unfold actionA
      rw [step107o373s56_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 360 * (codeMat 458 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 93) (codeMat 458) (codeMat 96) = codeMat 34 := by
      unfold actionA
      rw [step107o373s56_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 96 * (codeMat 458 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 374 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 374 (by decide)
    have hact : actionA (codeMat 93) (codeMat 458) (codeMat 374) = codeMat 74 := by
      unfold actionA
      rw [step107o373s56_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 374 * (codeMat 458 : Mat3).transpose = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 245 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 245 (by decide)
    have hact : actionA (codeMat 93) (codeMat 458) (codeMat 245) = codeMat 136 := by
      unfold actionA
      rw [step107o373s56_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 245 * (codeMat 458 : Mat3).transpose = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 500 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 500 (by decide)
    have hact : actionA (codeMat 93) (codeMat 458) (codeMat 500) = codeMat 266 := by
      unfold actionA
      rw [step107o373s56_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 500 * (codeMat 458 : Mat3).transpose = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step107o373_codeMat_mem_actionW_of_witness hw hact

theorem step107_o373_row56_qr : QuotientRankAtLeast step107o373ActualSource56 12 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 458 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 458) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 458) hP hQ orbit14W 12 orbit14_lb12
  have hMono : QuotientRankAtLeast step107o373ActualSource56 12 :=
    quotientRankAtLeast_mono step107o373s56_source_le_transport hAct
  exact quotientRankAtLeast_mono (by intro D hD; exact hD) hMono

/-- Preceding lower bound used to remove the zero quotient fiber for orbit 373. -/
theorem step107_o373_base_lb16 : QuotientRankAtLeast o373W 16 :=
  quotientRankAtLeast_mono step107_o373_row0_W_le_source step107_o373_row0_qr

/-- All original 57 orbit-373 source row lower bounds. -/
theorem step107_o373_row_qr (i : Fin 57) : QuotientRankAtLeast
    (match i.val with
    | 0 => step107o373ActualSource0
    | 1 => step107o373ActualSource1
    | 2 => step107o373ActualSource2
    | 3 => step107o373ActualSource3
    | 4 => step107o373ActualSource4
    | 5 => step107o373ActualSource5
    | 6 => step107o373ActualSource6
    | 7 => step107o373ActualSource7
    | 8 => step107o373ActualSource8
    | 9 => step107o373ActualSource9
    | 10 => step107o373ActualSource10
    | 11 => step107o373ActualSource11
    | 12 => step107o373ActualSource12
    | 13 => step107o373ActualSource13
    | 14 => step107o373ActualSource14
    | 15 => step107o373ActualSource15
    | 16 => step107o373ActualSource16
    | 17 => step107o373ActualSource17
    | 18 => step107o373ActualSource18
    | 19 => step107o373ActualSource19
    | 20 => step107o373ActualSource20
    | 21 => step107o373ActualSource21
    | 22 => step107o373ActualSource22
    | 23 => step107o373ActualSource23
    | 24 => step107o373ActualSource24
    | 25 => step107o373ActualSource25
    | 26 => step107o373ActualSource26
    | 27 => step107o373ActualSource27
    | 28 => step107o373ActualSource28
    | 29 => step107o373ActualSource29
    | 30 => step107o373ActualSource30
    | 31 => step107o373ActualSource31
    | 32 => step107o373ActualSource32
    | 33 => step107o373ActualSource33
    | 34 => step107o373ActualSource34
    | 35 => step107o373ActualSource35
    | 36 => step107o373ActualSource36
    | 37 => step107o373ActualSource37
    | 38 => step107o373ActualSource38
    | 39 => step107o373ActualSource39
    | 40 => step107o373ActualSource40
    | 41 => step107o373ActualSource41
    | 42 => step107o373ActualSource42
    | 43 => step107o373ActualSource43
    | 44 => step107o373ActualSource44
    | 45 => step107o373ActualSource45
    | 46 => step107o373ActualSource46
    | 47 => step107o373ActualSource47
    | 48 => step107o373ActualSource48
    | 49 => step107o373ActualSource49
    | 50 => step107o373ActualSource50
    | 51 => step107o373ActualSource51
    | 52 => step107o373ActualSource52
    | 53 => step107o373ActualSource53
    | 54 => step107o373ActualSource54
    | 55 => step107o373ActualSource55
    | 56 => step107o373ActualSource56
    | _ => step107o373ActualSource0)
    (match i.val with
    | 0 => 16
    | 1 => 16
    | 2 => 16
    | 3 => 15
    | 4 => 15
    | 5 => 15
    | 6 => 15
    | 7 => 14
    | 8 => 14
    | 9 => 14
    | 10 => 12
    | 11 => 12
    | 12 => 12
    | 13 => 12
    | 14 => 12
    | 15 => 12
    | 16 => 12
    | 17 => 12
    | 18 => 12
    | 19 => 9
    | 20 => 9
    | 21 => 9
    | 22 => 9
    | 23 => 9
    | 24 => 16
    | 25 => 15
    | 26 => 15
    | 27 => 15
    | 28 => 15
    | 29 => 14
    | 30 => 14
    | 31 => 12
    | 32 => 12
    | 33 => 12
    | 34 => 12
    | 35 => 12
    | 36 => 12
    | 37 => 9
    | 38 => 15
    | 39 => 14
    | 40 => 12
    | 41 => 12
    | 42 => 12
    | 43 => 12
    | 44 => 12
    | 45 => 12
    | 46 => 12
    | 47 => 12
    | 48 => 12
    | 49 => 12
    | 50 => 12
    | 51 => 9
    | 52 => 14
    | 53 => 12
    | 54 => 12
    | 55 => 12
    | 56 => 12
    | _ => 16) := by
  fin_cases i
  · exact step107_o373_row0_qr
  · exact step107_o373_row1_qr
  · exact step107_o373_row2_qr
  · exact step107_o373_row3_qr
  · exact step107_o373_row4_qr
  · exact step107_o373_row5_qr
  · exact step107_o373_row6_qr
  · exact step107_o373_row7_qr
  · exact step107_o373_row8_qr
  · exact step107_o373_row9_qr
  · exact step107_o373_row10_qr
  · exact step107_o373_row11_qr
  · exact step107_o373_row12_qr
  · exact step107_o373_row13_qr
  · exact step107_o373_row14_qr
  · exact step107_o373_row15_qr
  · exact step107_o373_row16_qr
  · exact step107_o373_row17_qr
  · exact step107_o373_row18_qr
  · exact step107_o373_row19_qr
  · exact step107_o373_row20_qr
  · exact step107_o373_row21_qr
  · exact step107_o373_row22_qr
  · exact step107_o373_row23_qr
  · exact step107_o373_row24_qr
  · exact step107_o373_row25_qr
  · exact step107_o373_row26_qr
  · exact step107_o373_row27_qr
  · exact step107_o373_row28_qr
  · exact step107_o373_row29_qr
  · exact step107_o373_row30_qr
  · exact step107_o373_row31_qr
  · exact step107_o373_row32_qr
  · exact step107_o373_row33_qr
  · exact step107_o373_row34_qr
  · exact step107_o373_row35_qr
  · exact step107_o373_row36_qr
  · exact step107_o373_row37_qr
  · exact step107_o373_row38_qr
  · exact step107_o373_row39_qr
  · exact step107_o373_row40_qr
  · exact step107_o373_row41_qr
  · exact step107_o373_row42_qr
  · exact step107_o373_row43_qr
  · exact step107_o373_row44_qr
  · exact step107_o373_row45_qr
  · exact step107_o373_row46_qr
  · exact step107_o373_row47_qr
  · exact step107_o373_row48_qr
  · exact step107_o373_row49_qr
  · exact step107_o373_row50_qr
  · exact step107_o373_row51_qr
  · exact step107_o373_row52_qr
  · exact step107_o373_row53_qr
  · exact step107_o373_row54_qr
  · exact step107_o373_row55_qr
  · exact step107_o373_row56_qr

end QiushiMatmul
