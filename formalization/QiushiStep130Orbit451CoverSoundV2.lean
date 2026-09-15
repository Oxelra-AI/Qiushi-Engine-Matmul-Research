import QiushiStep128Orbit451Defs

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open BigOperators Finset Matrix
namespace QiushiMatmul

-- Local public copies of the private simplification lemmas used in the generated Defs file.
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

/-- Soundness of the orbit451 scalar cover predicate: if the Boolean cover
predicate selects source `i` for a matrix `M`, then `M` belongs to the
corresponding scalar-annihilator source subspace.  The proof is intentionally
not by `native_decide` or by Decidable synthesis on submodule membership; it
follows the orbit450 pattern and explicitly simplifies both sides to the same
coordinate equations, then extracts the proposition from the closed Boolean
check. -/
theorem o451CoverSound (i : Fin 44) (M : Mat3) (h : o451Cover i M) :
    M ∈ o451SourceU i := by
  fin_cases i <;>
    simp only [o451Cover, o451ScalarCoverB, o451SourceU, o451AnnBasis,
      Submodule.mem_inf, mem_kEF_iff, evalFunc_add_left_local,
      o451_funcExp_30, o451_funcExp_36, o451_funcExp_58, o451_funcExp_68,
      o451_funcExp_90, o451_funcExp_94, o451_funcExp_96, o451_funcExp_100,
      o451_funcExp_122, o451_funcExp_132, o451_funcExp_154, o451_funcExp_158,
      o451_funcExp_160, o451_funcExp_164, o451_funcExp_190, o451_funcExp_196,
      o451_funcExp_224, o451_funcExp_250, o451_funcExp_254, o451_funcExp_267,
      o451_funcExp_271, o451_funcExp_299, o451_funcExp_303, o451_funcExp_305,
      o451_funcExp_331, o451_funcExp_335, o451_funcExp_337, o451_funcExp_363,
      o451_funcExp_369, o451_funcExp_395, o451_funcExp_401, o451_funcExp_405,
      o451_funcExp_431, o451_funcExp_491, o451_funcExp_501] at h ⊢ <;>
    exact of_decide_eq_true h

end QiushiMatmul
