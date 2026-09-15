import QiushiGlobalOrbitNormalizer

namespace QiushiMatmul.Calibration

open GlobalOrbit

/-- Two exact span inclusions and the label of the named frozen representative.
The source list order is significant for the backward XOR masks. -/
def RowOrbitCheck (source : List Nat) (label : Nat) (t : Transition) : Prop :=
  SpanCheck source ((frozenWangBasis t.target).map (wordCode t.word))
    t.forward t.backward ∧ frozenWangLower t.target = label

instance (source : List Nat) (label : Nat) (t : Transition) :
    Decidable (RowOrbitCheck source label t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem rowOrbitCheck_orbit (source : List Nat) (label : Nat) (t : Transition)
    (h : RowOrbitCheck source label t) :
    frozenWangTable.OrbitImage t.target (spanCodes source) := by
  apply (frozen_image_iff _ _).mpr
  rw [spanCheck_sound _ _ _ _ h.1,
    word_spanCodes _ _ (frozen_codes_bounded t.target)]
  exact wordSpace_equivalent _ _

/-- This premise is discharged by `FrozenLabel.L0_exact_of_orbit`, not by a
lower-bound certificate or the fact that every subspace has an orbit. -/
theorem rowOrbitCheck_exact
    (hExactOrbit : ∀ k : Fin 496, ∀ U : Submodule F2 Mat3,
      frozenWangTable.OrbitImage k U → frozenWangTable.L0 U = frozenWangLower k)
    (source : List Nat) (label : Nat) (t : Transition)
    (h : RowOrbitCheck source label t) :
    frozenWangTable.L0 (spanCodes source) = label :=
  (hExactOrbit t.target _ (rowOrbitCheck_orbit source label t h)).trans h.2

end QiushiMatmul.Calibration
