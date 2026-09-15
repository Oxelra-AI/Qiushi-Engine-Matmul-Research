import QiushiLineOrbit
import QiushiConversion
import QiushiOccupation

/-!
# Distinctness of nonzero A-factor lines at length 20

If two distinct indices generated the same nonzero A-line, both indices would
be killed by quotienting through that line.  The line lower bound and the
occupation inequality permit at most `20 - 19 = 1` killed index.
-/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

theorem A_line_distinct_from_line_bounds
    (P : FinitePremises) (D : TensorEntryDecomp 20)
    (s t : Fin 20) :
    D.A s ≠ 0 → D.A t ≠ 0 →
    Submodule.span F2 ({D.A s} : Set Mat3) =
      Submodule.span F2 ({D.A t} : Set Mat3) →
    s = t := by
  intro hs _ht hspan
  by_contra hst
  let W : Submodule F2 Mat3 := Submodule.span F2 ({D.A s} : Set Mat3)
  have hW : QuotientRankAtLeast W 19 := nonzero_line_lb19 P (D.A s) hs
  let D0 : QuotientTensorDecomp (⊥ : Submodule F2 Mat3) 20 :=
    entrywise_to_quotient D ⊥
  have hsW : D0.A s ∈ W := by
    change D.A s ∈ Submodule.span F2 ({D.A s} : Set Mat3)
    exact Submodule.mem_span_singleton_self (R := F2) (D.A s)
  have htW : D0.A t ∈ W := by
    change D.A t ∈ Submodule.span F2 ({D.A s} : Set Mat3)
    rw [hspan]
    exact Submodule.mem_span_singleton_self (R := F2) (D.A t)
  have hsKill : s ∈ killSet D0 W := by simp [killSet, hsW]
  have htKill : t ∈ killSet D0 W := by simp [killSet, htW]
  have hpairSubset : ({s, t} : Finset (Fin 20)) ⊆ killSet D0 W := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hsKill
    · have hut : u = t := Finset.mem_singleton.mp hu
      subst u
      exact htKill
  have hpairCard : ({s, t} : Finset (Fin 20)).card = 2 := by
    simp [hst]
  have hpairCardLe : ({s, t} : Finset (Fin 20)).card ≤
      (killSet D0 W).card := Finset.card_le_card hpairSubset
  have hkillTwo : 2 ≤ (killSet D0 W).card := by
    omega
  have hoccupation : (killSet D0 W).card ≤ 20 - 19 :=
    occupation_inequality (show (⊥ : Submodule F2 Mat3) ≤ W from bot_le)
      D0 hW (by omega)
  omega

end QiushiMatmul
end
