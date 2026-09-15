import QiushiFrozenWangData
import QiushiAllHighCountBridge

namespace QiushiMatmul.FrozenL0Report

open AllHighCount

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def clampCode (n : Nat) : Fin 512 :=
  ⟨n &&& 511, Nat.and_le_right.trans_lt (by decide)⟩

/-- Duplicate-free enumeration, with no independence assumption on the input. -/
def spanEnum : List Nat -> Finset (Fin 512)
  | [] => {0}
  | b :: bs => spanEnum bs ∪ (spanEnum bs).image (xorCode (clampCode b))

theorem mem_spanEnum (bs : List Nat) (c : Fin 512) :
    c ∈ spanEnum bs ↔ codeMat c.val ∈ spanCodes bs := by
  induction bs generalizing c with
  | nil =>
    have hzero : codeMat c.val = 0 ↔ c = 0 := by
      rw [← codeMat_zero]
      change matrixCodeEquiv c = matrixCodeEquiv 0 ↔ c = 0
      exact matrixCodeEquiv.injective.eq_iff
    simp [spanEnum, spanCodes, hzero]
  | cons b bs ih =>
    have hset : {M : Mat3 | ∃ n ∈ b :: bs, M = codeMat n} =
        insert (codeMat b) {M : Mat3 | ∃ n ∈ bs, M = codeMat n} := by
      ext M
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_insert_iff]
      aesop
    have hx (d : Fin 512) :
        codeMat (xorCode (clampCode b) d).val = codeMat b + codeMat d.val := by
      change codeMat (Nat.xor (b &&& 511) d.val) = _
      exact (codeMat_xor (b &&& 511) d.val).trans
        (congrArg (fun M => M + codeMat d.val) (codeMat_and_511 b))
    rw [spanEnum, Finset.mem_union, Finset.mem_image]
    change (_ ∨ _) ↔ codeMat c.val ∈ Submodule.span F2 _
    rw [hset, Submodule.mem_span_insert]
    constructor
    · rintro (hc | ⟨d, hd, rfl⟩)
      · exact ⟨0, codeMat c.val, (ih c).mp hc, by simp⟩
      · exact ⟨1, codeMat d.val, (ih d).mp hd, by simpa using hx d⟩
    · rintro ⟨a, M, hM, heq⟩
      change M ∈ spanCodes bs at hM
      rcases scalar_cases a with rfl | rfl
      · left
        apply (ih c).mpr
        rw [heq]
        simpa using hM
      · right
        refine ⟨matrixCodeEquiv.symm M, ?_, ?_⟩
        · apply (ih _).mpr
          change matrixCodeEquiv (matrixCodeEquiv.symm M) ∈ spanCodes bs
          simpa using hM
        · apply matrixCodeEquiv.injective
          change codeMat (xorCode (clampCode b) (matrixCodeEquiv.symm M)).val = codeMat c.val
          rw [hx, show codeMat (matrixCodeEquiv.symm M).val = M from
            matrixCodeEquiv.apply_symm_apply M]
          simpa using heq.symm

noncomputable def spanEnumEquiv (bs : List Nat) :
    {c // c ∈ spanEnum bs} ≃ spanCodes bs :=
  matrixCodeEquiv.subtypeEquiv (mem_spanEnum bs)

noncomputable def rankCount (W : Submodule F2 Mat3) (r : Nat) : Nat :=
  Nat.card {M : W // (M : Mat3).rank = r}

def codeRankCount (bs : List Nat) (r : Nat) : Nat :=
  ((spanEnum bs).filter fun c => rankCode c.val = r).card

theorem spanEnum_card (bs : List Nat) : (spanEnum bs).card = Nat.card (spanCodes bs) := by
  rw [← Nat.card_congr (spanEnumEquiv bs), Nat.card_eq_fintype_card]
  exact (Fintype.card_coe _).symm

theorem codeRankCount_correct (bs : List Nat) (r : Nat) :
    codeRankCount bs r = rankCount (spanCodes bs) r := by
  classical
  let e := (spanEnumEquiv bs).subtypeEquiv
    (p := fun c : {c // c ∈ spanEnum bs} => rankCode c.val.val = r)
    (q := fun M : spanCodes bs => (M : Mat3).rank = r)
    (fun c => by change rankCode c.val.val = r ↔ (codeMat c.val.val).rank = r
                 rw [rank_eq_rankCode_code])
  let e0 : {c // c ∈ (spanEnum bs).filter (fun c => rankCode c.val = r)} ≃
      {c : {c // c ∈ spanEnum bs} // rankCode c.val.val = r} :=
    { toFun := fun c => ⟨⟨c.val, (Finset.mem_filter.mp c.property).1⟩,
        (Finset.mem_filter.mp c.property).2⟩
      invFun := fun c => ⟨c.val.val, Finset.mem_filter.mpr ⟨c.val.property, c.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    codeRankCount bs r = Nat.card
        {c // c ∈ (spanEnum bs).filter (fun c => rankCode c.val = r)} := by
      simp only [codeRankCount, Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = rankCount (spanCodes bs) r := Nat.card_congr (e0.trans e)

theorem map_counts (f : Mat3 →ₗ[F2] Mat3) (hf : Function.Injective f)
    (hr : ∀ M, (f M).rank = M.rank) (W : Submodule F2 Mat3) :
    Nat.card (W.map f) = Nat.card W ∧ ∀ r, rankCount (W.map f) r = rankCount W r := by
  let e := (Submodule.equivMapOfInjective f hf W).toEquiv
  constructor
  · exact (Nat.card_congr e).symm
  · intro r
    exact (Nat.card_congr (e.subtypeEquiv
      (p := fun M : W => (M : Mat3).rank = r)
      (q := fun M : W.map f => (M : Mat3).rank = r)
      (fun M => by change M.val.rank = r ↔ (f M.val).rank = r; rw [hr]))).symm

theorem orbit_counts (i : Fin 496) (W : Submodule F2 Mat3)
    (h : frozenWangTable.OrbitImage i W) :
    Nat.card W = (spanEnum (frozenWangBasis i)).card ∧
      ∀ r, rankCount W r = codeRankCount (frozenWangBasis i) r := by
  obtain ⟨P, Q, ⟨hP⟩, ⟨hQ⟩, flip, rfl⟩ := h
  let := hP
  let := hQ
  have ha := map_counts (actionALinearMap P Q)
    (Function.LeftInverse.injective (pullbackA_actionA (P := P) (Q := Q)))
    (fun M => ah_action_rank_eq P Q M)
  have ht := map_counts transposeLinearMap Matrix.transpose_injective Matrix.rank_transpose
  simp only [spanEnum_card, codeRankCount_correct]
  cases flip with
  | false => exact ha _
  | true =>
    obtain ⟨hc, hr⟩ := ha (transposeW (spanCodes (frozenWangBasis i)))
    obtain ⟨htc, htr⟩ := ht (spanCodes (frozenWangBasis i))
    exact ⟨hc.trans htc, fun r => (hr r).trans (htr r)⟩

/-- Only higher labels must be excluded; orbit uniqueness is unnecessary. -/
theorem L0_le_of_orbit_labels (W : Submodule F2 Mat3) (n : Nat)
    (h : ∀ i, frozenWangTable.OrbitImage i W → frozenWangLower i ≤ n) :
    frozenWangTable.L0 W ≤ n := by
  classical
  apply Finset.sup_le
  intro i _
  split_ifs with hi
  · exact h i hi
  · exact Nat.zero_le n

end QiushiMatmul.FrozenL0Report
