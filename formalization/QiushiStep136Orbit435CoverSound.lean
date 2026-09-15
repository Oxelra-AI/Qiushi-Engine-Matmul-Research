import QiushiStep136Orbit435Defs

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open BigOperators Finset Matrix
namespace QiushiMatmul

private lemma mem_kEF_iff {L M : Mat3} : M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

private theorem evalFunc_add_left_local (L N M : Mat3) :
    evalFunc (L + N) M = evalFunc L M + evalFunc N M := by
  unfold evalFunc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  show (L + N) i j * M i j = L i j * M i j + N i j * M i j
  rw [show (L + N) i j = L i j + N i j from rfl, add_mul]

theorem o435CoverSound (i : Fin 63) (M : Mat3) (h : o435Cover i M) :
    M ∈ o435SourceU i := by
  fin_cases i <;>
    simp only [o435Cover, o435ScalarCoverB, o435SourceU, o435AnnBasis, Submodule.mem_inf, mem_kEF_iff, evalFunc_add_left_local, o435_funcExp_30, o435_funcExp_58, o435_funcExp_62, o435_funcExp_75, o435_funcExp_79, o435_funcExp_81, o435_funcExp_85, o435_funcExp_113, o435_funcExp_139, o435_funcExp_143, o435_funcExp_149, o435_funcExp_171, o435_funcExp_175, o435_funcExp_177, o435_funcExp_181, o435_funcExp_196, o435_funcExp_218, o435_funcExp_222, o435_funcExp_224, o435_funcExp_228, o435_funcExp_250, o435_funcExp_254, o435_funcExp_260, o435_funcExp_282, o435_funcExp_286, o435_funcExp_288, o435_funcExp_314, o435_funcExp_318, o435_funcExp_331, o435_funcExp_337, o435_funcExp_395, o435_funcExp_401, o435_funcExp_405, o435_funcExp_427, o435_funcExp_433, o435_funcExp_452, o435_funcExp_478, o435_funcExp_480, o435_funcExp_484] at h ⊢ <;>
    exact of_decide_eq_true h

end QiushiMatmul
