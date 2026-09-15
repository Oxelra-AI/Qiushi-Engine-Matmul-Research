import QiushiDirectCoverage
import QiushiLineOrbit
import QiushiCodeSpanBridgeCore
import QiushiMatmulFinitePremises
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiMonoOrbit478From412
import QiushiMonoOrbit479GradedFrom417

/-! Shared definitions for the split direct singleton-cover proof. -/
set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
namespace QiushiMatmul

def linePlane478 : Submodule F2 Mat3 := spanCodes [2, 1]
def linePlane479 : Submodule F2 Mat3 := spanCodes [1, 10]
def linePlane480 : Submodule F2 Mat3 := spanCodes [16, 1]
def linePlane481 : Submodule F2 Mat3 := spanCodes [20, 1]
def linePlane482 : Submodule F2 Mat3 := spanCodes [84, 1]
def linePlane483 : Submodule F2 Mat3 := spanCodes [160, 1]
def linePlane478T : Submodule F2 Mat3 := spanCodes [8, 1]
def linePlane481T : Submodule F2 Mat3 := spanCodes [80, 1]

theorem linePlane478T_lb (h : QuotientRankAtLeast linePlane478 17) :
    QuotientRankAtLeast linePlane478T 17 := by
  have ht := quotientRankAtLeast_transpose h
  have hle : linePlane478T ≤ transposeW linePlane478 := by
    unfold linePlane478T transposeW linePlane478
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
    rcases hn with h0 | h1
    · subst h0
      show codeMat 8 ∈ Submodule.map transposeLinearMap (spanCodes [2, 1])
      exact ⟨codeMat 2, spanContainsCode_implies_mem_spanCodes [2, 1] 2 (by decide), by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 1 ∈ Submodule.map transposeLinearMap (spanCodes [2, 1])
      exact ⟨codeMat 1, spanContainsCode_implies_mem_spanCodes [2, 1] 1 (by decide), by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

theorem linePlane481T_lb (h : QuotientRankAtLeast linePlane481 18) :
    QuotientRankAtLeast linePlane481T 18 := by
  have ht := quotientRankAtLeast_transpose h
  have hle : linePlane481T ≤ transposeW linePlane481 := by
    unfold linePlane481T transposeW linePlane481
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
    rcases hn with h0 | h1
    · subst h0
      show codeMat 80 ∈ Submodule.map transposeLinearMap (spanCodes [20, 1])
      exact ⟨codeMat 20, spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide), by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 1 ∈ Submodule.map transposeLinearMap (spanCodes [20, 1])
      exact ⟨codeMat 1, spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide), by ext i j <;> fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

def lineSourceCode (i : Fin 255) : Nat := 2 * (i.val + 1)
def lineSourcePlane (i : Fin 255) : Submodule F2 Mat3 := spanCodes [1, lineSourceCode i]
def lineSourceLb (i : Fin 255) : Nat :=
  match i.val with
  | 0 => 17
  | 1 => 17
  | 2 => 17
  | 3 => 17
  | 4 => 17
  | 5 => 17
  | 6 => 17
  | 7 => 18
  | 8 => 18
  | 9 => 18
  | 10 => 18
  | 11 => 18
  | 12 => 18
  | 13 => 18
  | 14 => 18
  | 15 => 18
  | 16 => 18
  | 17 => 18
  | 18 => 18
  | 19 => 18
  | 20 => 18
  | 21 => 18
  | 22 => 18
  | 23 => 18
  | 24 => 18
  | 25 => 18
  | 26 => 18
  | 27 => 18
  | 28 => 18
  | 29 => 18
  | 30 => 18
  | 31 => 17
  | 32 => 17
  | 33 => 17
  | 34 => 17
  | 35 => 17
  | 36 => 17
  | 37 => 17
  | 38 => 17
  | 39 => 18
  | 40 => 18
  | 41 => 18
  | 42 => 18
  | 43 => 18
  | 44 => 18
  | 45 => 18
  | 46 => 18
  | 47 => 18
  | 48 => 18
  | 49 => 18
  | 50 => 18
  | 51 => 18
  | 52 => 18
  | 53 => 18
  | 54 => 18
  | 55 => 18
  | 56 => 18
  | 57 => 18
  | 58 => 18
  | 59 => 18
  | 60 => 18
  | 61 => 18
  | 62 => 18
  | 63 => 18
  | 64 => 18
  | 65 => 18
  | 66 => 18
  | 67 => 18
  | 68 => 18
  | 69 => 18
  | 70 => 18
  | 71 => 18
  | 72 => 18
  | 73 => 18
  | 74 => 18
  | 75 => 18
  | 76 => 18
  | 77 => 18
  | 78 => 18
  | 79 => 18
  | 80 => 18
  | 81 => 18
  | 82 => 18
  | 83 => 18
  | 84 => 18
  | 85 => 18
  | 86 => 18
  | 87 => 18
  | 88 => 18
  | 89 => 18
  | 90 => 18
  | 91 => 18
  | 92 => 18
  | 93 => 18
  | 94 => 18
  | 95 => 18
  | 96 => 18
  | 97 => 18
  | 98 => 18
  | 99 => 18
  | 100 => 18
  | 101 => 18
  | 102 => 18
  | 103 => 18
  | 104 => 18
  | 105 => 18
  | 106 => 18
  | 107 => 18
  | 108 => 18
  | 109 => 18
  | 110 => 18
  | 111 => 18
  | 112 => 18
  | 113 => 18
  | 114 => 18
  | 115 => 18
  | 116 => 18
  | 117 => 18
  | 118 => 18
  | 119 => 18
  | 120 => 18
  | 121 => 18
  | 122 => 18
  | 123 => 18
  | 124 => 18
  | 125 => 18
  | 126 => 18
  | 127 => 18
  | 128 => 18
  | 129 => 18
  | 130 => 18
  | 131 => 18
  | 132 => 18
  | 133 => 18
  | 134 => 18
  | 135 => 18
  | 136 => 18
  | 137 => 18
  | 138 => 18
  | 139 => 18
  | 140 => 18
  | 141 => 18
  | 142 => 18
  | 143 => 18
  | 144 => 18
  | 145 => 18
  | 146 => 18
  | 147 => 18
  | 148 => 18
  | 149 => 18
  | 150 => 18
  | 151 => 18
  | 152 => 18
  | 153 => 18
  | 154 => 18
  | 155 => 18
  | 156 => 18
  | 157 => 18
  | 158 => 18
  | 159 => 18
  | 160 => 18
  | 161 => 18
  | 162 => 18
  | 163 => 18
  | 164 => 18
  | 165 => 18
  | 166 => 18
  | 167 => 18
  | 168 => 18
  | 169 => 18
  | 170 => 18
  | 171 => 18
  | 172 => 18
  | 173 => 18
  | 174 => 18
  | 175 => 18
  | 176 => 18
  | 177 => 18
  | 178 => 18
  | 179 => 18
  | 180 => 18
  | 181 => 18
  | 182 => 18
  | 183 => 18
  | 184 => 18
  | 185 => 18
  | 186 => 18
  | 187 => 18
  | 188 => 18
  | 189 => 18
  | 190 => 18
  | 191 => 18
  | 192 => 18
  | 193 => 18
  | 194 => 18
  | 195 => 18
  | 196 => 18
  | 197 => 18
  | 198 => 18
  | 199 => 18
  | 200 => 18
  | 201 => 18
  | 202 => 18
  | 203 => 18
  | 204 => 18
  | 205 => 18
  | 206 => 18
  | 207 => 18
  | 208 => 18
  | 209 => 18
  | 210 => 18
  | 211 => 18
  | 212 => 18
  | 213 => 18
  | 214 => 18
  | 215 => 18
  | 216 => 18
  | 217 => 18
  | 218 => 18
  | 219 => 18
  | 220 => 18
  | 221 => 18
  | 222 => 18
  | 223 => 18
  | 224 => 18
  | 225 => 18
  | 226 => 18
  | 227 => 18
  | 228 => 18
  | 229 => 18
  | 230 => 18
  | 231 => 18
  | 232 => 18
  | 233 => 18
  | 234 => 18
  | 235 => 18
  | 236 => 18
  | 237 => 18
  | 238 => 18
  | 239 => 18
  | 240 => 18
  | 241 => 18
  | 242 => 18
  | 243 => 18
  | 244 => 18
  | 245 => 18
  | 246 => 18
  | 247 => 18
  | 248 => 18
  | 249 => 18
  | 250 => 18
  | 251 => 18
  | 252 => 18
  | 253 => 18
  | 254 => 18
  | _ => 18

def lineCoverB (i : Fin 255) (M : Mat3) : Bool :=
  spanContainsCode [1, lineSourceCode i] (matrixCodeNat M)

theorem lineCoverSound (i : Fin 255) (M : Mat3) :
    lineCoverB i M = true → M ∈ lineSourcePlane i := by
  intro h
  unfold lineCoverB at h
  unfold lineSourcePlane
  rw [← codeMat_matrixCode M]
  exact spanContainsCode_implies_mem_spanCodes [1, lineSourceCode i] (matrixCodeNat M) h

theorem lineMatCoverage : ∀ M : Mat3,
    1 ≤ ∑ i : Fin 255, if lineCoverB i M = true then 1 else 0 := by
  intro M
  revert M
  decide

theorem direct_coverage_quotient_decomp_false_of_boolEq_cover
    {m r : ℕ}
    {W : Submodule F2 Mat3}
    (sourceU : Fin m → Submodule F2 Mat3)
    (sourceLb : Fin m → ℕ)
    (lambda : Fin m → ℕ) (lambda0 target : ℕ)
    (cover : Fin m → Mat3 → Bool)
    (hWU : ∀ i : Fin m, W ≤ sourceU i)
    (hSource : ∀ i : Fin m, QuotientRankAtLeast (sourceU i) (sourceLb i))
    (hLambda : lambda0 ≤ ∑ i : Fin m, lambda i)
    (hCoverSound : ∀ (i : Fin m) (M : Mat3), cover i M = true → M ∈ sourceU i)
    (hMatCov : ∀ M : Mat3, lambda0 ≤ ∑ i : Fin m,
      if cover i M = true then lambda i else 0)
    (hrt : r ≤ target)
    (hCert : ((∑ i : Fin m, lambda i) - lambda0) * target <
        ∑ i : Fin m, lambda i * sourceLb i)
    (D : QuotientTensorDecomp W r) :
    False := by
  classical
  by_cases hAllLe : ∀ i : Fin m, sourceLb i ≤ r
  · have hTermCov : ∀ t : Fin r,
        lambda0 ≤ ∑ i : Fin m,
          if t ∈ killSet D (sourceU i) then lambda i else 0 := by
      intro t
      have hMat := hMatCov (D.A t)
      refine le_trans hMat ?_
      apply Finset.sum_le_sum
      intro i _
      by_cases hc : cover i (D.A t) = true
      · have ht : t ∈ killSet D (sourceU i) := by
          simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hCoverSound i (D.A t) hc
        simp [hc, ht]
      · have hf : cover i (D.A t) = false := by
          cases hb : cover i (D.A t) <;> simp_all
        simp [hf]
    have hRowsAdd : ∀ i : Fin m,
        (killSet D (sourceU i)).card + sourceLb i ≤ r := by
      intro i
      have hk : (killSet D (sourceU i)).card ≤ r - sourceLb i :=
        occupation_inequality (hWU i) D (hSource i) (hAllLe i)
      calc (killSet D (sourceU i)).card + sourceLb i
          ≤ (r - sourceLb i) + sourceLb i :=
            Nat.add_le_add_right hk (sourceLb i)
        _ = r := Nat.sub_add_cancel (hAllLe i)
    exact weighted_cover_infeasible_from_term_coverage
      (fun i => killSet D (sourceU i)) sourceLb lambda lambda0 target
      hLambda hTermCov hRowsAdd hrt hCert
  · push Not at hAllLe
    rcases hAllLe with ⟨i, hi⟩
    exact quotient_bound_exceeds_length (hWU i) D (hSource i) hi

theorem lineRank1_le_source (i : Fin 255) : lineRank1 ≤ lineSourcePlane i := by
  unfold lineRank1 lineSourcePlane spanCodes
  apply Submodule.span_mono
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
  subst hn
  exact ⟨1, by simp, rfl⟩

theorem line478_ledger : QuotientRankAtLeast linePlane478 17 := by
  simpa [linePlane478, o478W_mono] using orbit478_lb17_mono
theorem line479_ledger : QuotientRankAtLeast linePlane479 17 := by
  simpa [linePlane479, o479W_graded] using orbit479_lb17_graded

end QiushiMatmul
