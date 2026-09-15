import QiushiGlobalOrbitDuality

/-! Small rank and annihilator certificates, with arbitrary-dimensional semantic spans. -/
open Matrix BigOperators
namespace QiushiMatmul.GlobalOrbit
open PlaneOrbit QuotientRestriction
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def BasisCheck (bs ds : List Nat) : Prop :=
  ∀ i j : Fin bs.length, matrixDual (codeMat (ds.getD i.val 0)) (codeMat bs[j.val]) =
    if i = j then 1 else 0

instance (bs ds : List Nat) : Decidable (BasisCheck bs ds) :=
  inferInstanceAs (Decidable (∀ i j : Fin bs.length,
    matrixDual (codeMat (ds.getD i.val 0)) (codeMat bs[j.val]) = if i = j then 1 else 0))

theorem basis_independent (bs ds : List Nat) (h : BasisCheck bs ds) :
    LinearIndependent F2 (fun j : Fin bs.length => codeMat bs[j.val]) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have hi := congrArg (matrixDual (codeMat (ds.getD i.val 0))) hg
  dsimp only [BasisCheck] at h
  simp only [map_sum, map_smul, map_zero] at hi
  simp_rw [h] at hi
  simpa using hi

theorem basis_dimension (bs ds : List Nat) (h : BasisCheck bs ds) :
    Module.finrank F2 (spanCodes bs) = bs.length := by
  have he : spanCodes bs = Submodule.span F2
      (Set.range (fun j : Fin bs.length => codeMat bs[j.val])) := by
    unfold spanCodes
    congr 1
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, List.getElem_mem i.isLt, rfl⟩
  rw [he, finrank_span_eq_card (basis_independent bs ds h), Fintype.card_fin]

def wordCode : List (Fin 4) → Nat → Nat
  | [], c => c
  | g :: gs, c => genCode g (wordCode gs c)

def wordSpace : List (Fin 4) → Space → Space
  | [], W => W
  | g :: gs, W => genW g (wordSpace gs W)

theorem wordCode_bound (w : List (Fin 4)) {c : Nat} (hc : c < 512) : wordCode w c < 512 := by
  induction w with
  | nil => exact hc
  | cons g gs ih => exact genCode_bound g ⟨wordCode gs c, ih⟩

theorem wordSpace_equivalent (w : List (Fin 4)) (W : Space) : Equivalent W (wordSpace w W) := by
  induction w with
  | nil => exact equivalent_refl _
  | cons g gs ih => exact equivalent_trans ih (generator_equivalent g _)

theorem wordSpace_dimension (w : List (Fin 4)) (W : Space) :
    Module.finrank F2 (wordSpace w W) = Module.finrank F2 W := by
  induction w with
  | nil => rfl
  | cons g gs ih =>
    change Module.finrank F2 ((wordSpace gs W).map (genEquiv g).toLinearMap) = _
    rw [LinearEquiv.finrank_map_eq, ih]

theorem gen_spanCodes (g : Fin 4) (bs : List Nat) (hb : ∀ c ∈ bs, c < 512) :
    spanCodes (bs.map (genCode g)) = genW g (spanCodes bs) := by
  unfold spanCodes genW
  rw [Submodule.map_span]
  congr 1
  ext M
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨codeMat c, ⟨c, hc, rfl⟩, (genCode_semantics g ⟨c, hb c hc⟩).symm⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨genCode g c, ⟨c, hc, rfl⟩, (genCode_semantics g ⟨c, hb c hc⟩).symm⟩

theorem word_spanCodes (w : List (Fin 4)) (bs : List Nat) (hb : ∀ c ∈ bs, c < 512) :
    spanCodes (bs.map (wordCode w)) = wordSpace w (spanCodes bs) := by
  induction w with
  | nil => simp [wordCode, wordSpace]
  | cons g gs ih =>
    change spanCodes (bs.map (genCode g ∘ wordCode gs)) = _
    rw [← List.map_map, gen_spanCodes, ih]
    · rfl
    · intro c hc
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
      exact wordCode_bound gs (hb a ha)

theorem spanCodes_le_dual (bs cs : List Nat)
    (h : ∀ a ∈ bs, ∀ c ∈ cs, matrixDual (codeMat a) (codeMat c) = 0) :
    spanCodes cs ≤ dual (spanCodes bs) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨c, hc, rfl⟩
  change codeMat c ∈ inputAnnihilator (spanCodes bs)
  rw [mem_inputAnnihilator]
  have hker : spanCodes bs ≤ LinearMap.ker (matrixDual (codeMat c)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change matrixDual (codeMat c) (codeMat a) = 0
    rw [matrixDual_comm]
    exact h a ha c hc
  intro A hA
  rw [matrixDual_comm]
  exact hker hA

/-- Only ranks and generator images are checked, not all members of the annihilator. -/
theorem dual_eq_word (bs ds cs es : List Nat) (w : List (Fin 4))
    (hb : BasisCheck bs ds) (hc : BasisCheck cs es)
    (hbound : ∀ c ∈ cs, c < 512) (hlen : bs.length + cs.length = 9)
    (horth : ∀ a ∈ bs, ∀ c ∈ cs,
      matrixDual (codeMat a) (codeMat (wordCode w c)) = 0) :
    dual (spanCodes bs) = wordSpace w (spanCodes cs) := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← word_spanCodes w cs hbound]
    apply spanCodes_le_dual
    intro a ha c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact horth a ha b hb
  · rw [wordSpace_dimension, basis_dimension cs es hc]
    have hd := dual_dimension (spanCodes bs)
    rw [basis_dimension bs ds hb] at hd
    omega

end QiushiMatmul.GlobalOrbit
