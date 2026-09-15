import QiushiAllHighPlaneActions

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

lemma ah_spanCodes_pair (a b : Nat) :
    spanCodes [a, b] = Submodule.span F2 ({codeMat a, codeMat b} : Set Mat3) := by
  unfold spanCodes
  congr 1
  ext M
  simp

lemma ah_actionW_span_pair (P Q X Y : Mat3) :
    actionW P Q (Submodule.span F2 ({X, Y} : Set Mat3)) =
      Submodule.span F2 ({actionA P Q X, actionA P Q Y} : Set Mat3) := by
  rw [actionW, Submodule.map_span]
  congr 1
  ext Z
  simp [actionALinearMap, eq_comm]

lemma ah_add_self (X : Mat3) : X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

lemma ah_span_pair_add_right (X Y : Mat3) :
    Submodule.span F2 ({X, X + Y} : Set Mat3) =
      Submodule.span F2 ({X, Y} : Set Mat3) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with hZ | hZ
    · subst Z
      exact Submodule.subset_span (by simp)
    · subst Z
      exact (Submodule.span F2 ({X, Y} : Set Mat3)).add_mem
        (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with hZ | hZ
    · subst Z
      exact Submodule.subset_span (by simp)
    · subst Z
      have hXY : X + Y ∈ Submodule.span F2 ({X, X + Y} : Set Mat3) :=
        Submodule.subset_span (by simp)
      have hX : X ∈ Submodule.span F2 ({X, X + Y} : Set Mat3) :=
        Submodule.subset_span (by simp)
      have hsum := (Submodule.span F2 ({X, X + Y} : Set Mat3)).add_mem hX hXY
      have heq : X + (X + Y) = Y := by rw [← add_assoc, ah_add_self, zero_add]
      rwa [heq] at hsum

lemma ah_span_pair_add_left (X Y : Mat3) :
    Submodule.span F2 ({X + Y, Y} : Set Mat3) =
      Submodule.span F2 ({X, Y} : Set Mat3) := by
  calc
    Submodule.span F2 ({X + Y, Y} : Set Mat3) =
        Submodule.span F2 ({Y, Y + X} : Set Mat3) := by
          rw [Set.pair_comm (a := X + Y) (b := Y), add_comm]
    _ = Submodule.span F2 ({Y, X} : Set Mat3) := ah_span_pair_add_right Y X
    _ = Submodule.span F2 ({X, Y} : Set Mat3) := by rw [Set.pair_comm]

lemma ah_span_pair_add_swap (X Y : Mat3) :
    Submodule.span F2 ({X + Y, X} : Set Mat3) =
      Submodule.span F2 ({Y, X} : Set Mat3) := by
  rw [add_comm]
  exact ah_span_pair_add_left Y X

lemma ah_span_pick3_pair (X Y : Mat3) (i j : Fin 3) (hij : i ≠ j) :
    Submodule.span F2 ({ahPick3 X Y i, ahPick3 X Y j} : Set Mat3) =
      Submodule.span F2 ({X, Y} : Set Mat3) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [ahPick3, Set.pair_comm, ah_span_pair_add_right,
      ah_span_pair_add_left, ah_span_pair_add_swap]

lemma ah_transposeW_span_pair (X Y : Mat3) :
    transposeW (Submodule.span F2 ({X, Y} : Set Mat3)) =
      Submodule.span F2 ({X.transpose, Y.transpose} : Set Mat3) := by
  rw [transposeW, Submodule.map_span]
  congr 1
  ext Z
  simp [transposeLinearMap, eq_comm]

lemma ah_source_span_selected (i : Fin 8) (tr : Bool) (sa sb : Fin 3)
    (hne : sa ≠ sb) :
    ahSourceW i tr =
      Submodule.span F2 ({ahSourcePick i tr sa, ahSourcePick i tr sb} : Set Mat3) := by
  cases tr
  · exact (ah_span_pick3_pair (ahPlaneM1 i) (ahPlaneM2 i) sa sb hne).symm
  · rw [ahSourceW, ahPlaneW, ah_transposeW_span_pair]
    exact (ah_span_pick3_pair (ahPlaneM1 i).transpose
      (ahPlaneM2 i).transpose sa sb hne).symm

lemma ah_plane_lb19 (P : FinitePremises) (i : Fin 8) :
    QuotientRankAtLeast (ahPlaneW i) 19 := by
  fin_cases i
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane484, ah_spanCodes_pair] using P.plane484_lb19
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane485, ah_spanCodes_pair] using P.plane485_lb19
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane486, ah_spanCodes_pair] using P.plane486_lb19
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane487, ah_spanCodes_pair] using P.plane487_lb19
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane488, ah_spanCodes_pair] using P.plane488_lb19
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane489, ah_spanCodes_pair] using P.plane489_lb19
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane490, ah_spanCodes_pair] using P.plane490_lb19
  · simpa [ahPlaneW, ahPlaneM1, ahPlaneM2, ahPlaneCode1, ahPlaneCode2,
      plane491, ah_spanCodes_pair] using P.plane491_lb19

end QiushiMatmul
end
