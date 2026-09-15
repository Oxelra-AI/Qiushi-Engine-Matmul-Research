import QiushiOccupationSystemBridge

open BigOperators

namespace QiushiMatmul.OccupationSystemBridge

/-- All strict proper superspace rows for an arbitrary table `L`. This does not
identify `L` with a historical table or make any tensor-realizability claim. -/
structure FullOccupation (cfg : PlaneExtConfig) (L : Submodule F2 Mat3 → Nat)
    (weight : Direction cfg.W → Int) : Prop where
  nonneg : ∀ q, 0 ≤ weight q
  total : (∑ q, weight q) = (cfg.target : Int)
  cap : ∀ U : Submodule F2 Mat3, cfg.W < U → U < ⊤ →
    quotientMass weight U ≤ (cfg.target : Int) - (L U : Int)

/-- Exact geometric and numeric conditions needed to use the full system's
rows. Proving these for a particular frozen table is a separate obligation. -/
structure FullOccupationBinding (cfg : PlaneExtConfig)
    (L : Submodule F2 Mat3 → Nat) : Prop where
  sourceStrict : ∀ i, cfg.W < cfg.sourceU i
  sourceProper : ∀ i, cfg.sourceU i < ⊤
  sourceLowerBound : ∀ i, cfg.sourceLb i ≤ L (cfg.sourceU i)
  deadStrict : ∀ d, cfg.W < cfg.deadU d
  deadProper : ∀ d, cfg.deadU d < ⊤
  deadLowerBound : ∀ d, cfg.target ≤ L (cfg.deadU d)

/-- Assemble separately proved paired geometric facts and numeric bindings. -/
theorem FullOccupationBinding.of_paired
    (cfg : PlaneExtConfig) (L : Submodule F2 Mat3 → Nat)
    (hSource : ∀ i, cfg.W < cfg.sourceU i ∧ cfg.sourceU i < ⊤)
    (hDead : ∀ d, cfg.W < cfg.deadU d ∧ cfg.deadU d < ⊤)
    (hSourceL : ∀ i, cfg.sourceLb i ≤ L (cfg.sourceU i))
    (hDeadL : ∀ d, cfg.target ≤ L (cfg.deadU d)) :
    FullOccupationBinding cfg L where
  sourceStrict i := (hSource i).1
  sourceProper i := (hSource i).2
  sourceLowerBound := hSourceL
  deadStrict d := (hDead d).1
  deadProper d := (hDead d).2
  deadLowerBound := hDeadL

theorem full_occupation_to_caps
    (cfg : PlaneExtConfig) (L : Submodule F2 Mat3 → Nat)
    (binding : FullOccupationBinding cfg L)
    (weight : Direction cfg.W → Int) (h : FullOccupation cfg L weight) :
    Caps cfg weight where
  nonneg := h.nonneg
  total := h.total.ge
  source := by
    intro i
    have hcap := h.cap (cfg.sourceU i) (binding.sourceStrict i) (binding.sourceProper i)
    apply hcap.trans
    apply sub_le_sub_left
    exact_mod_cast binding.sourceLowerBound i
  dead := by
    intro d
    have hcap := h.cap (cfg.deadU d) (binding.deadStrict d) (binding.deadProper d)
    apply hcap.trans
    apply sub_nonpos.mpr
    exact_mod_cast binding.deadLowerBound d

/-- Conditional full-system infeasibility, independent of tensor decompositions.
No assertion about the original frozen L0 or its CNF encoding is made. -/
theorem full_occupation_no_model
    (cfg : PlaneExtConfig) (hBool : PlaneExtBool cfg)
    (hNoModel : ∀ x : Fin cfg.nLive → Int, cfg.occSys.RootHolds x → False)
    (L : Submodule F2 Mat3 → Nat) (binding : FullOccupationBinding cfg L)
    (weight : Direction cfg.W → Int) (h : FullOccupation cfg L weight) : False :=
  quotient_counts_no_model cfg hBool hNoModel weight
    (full_occupation_to_caps cfg L binding weight h)

end QiushiMatmul.OccupationSystemBridge
