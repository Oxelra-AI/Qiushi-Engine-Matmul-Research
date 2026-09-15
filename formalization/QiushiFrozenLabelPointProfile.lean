import QiushiFrozenLabelCore

namespace QiushiMatmul.FrozenLabel

open FrozenL0Report AllHighCount

set_option maxHeartbeats 2000000

theorem filter_card_eq_natCard {A B : Type*} [DecidableEq A] (s : Finset A)
    (e : {a // a ∈ s} ≃ B) (p : A → Prop) [DecidablePred p] (q : B → Prop)
    (h : ∀ a, p a.val ↔ q (e a)) :
    (s.filter p).card = Nat.card {b : B // q b} := by
  let e0 : {a // a ∈ s.filter p} ≃ {a : {a // a ∈ s} // p a.val} :=
    { toFun := fun a => ⟨⟨a.val, (Finset.mem_filter.mp a.property).1⟩,
        (Finset.mem_filter.mp a.property).2⟩
      invFun := fun a => ⟨a.val.val, Finset.mem_filter.mpr ⟨a.val.property, a.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Nat.card {a // a ∈ s.filter p} := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := Nat.card_congr (e0.trans (e.subtypeEquiv h))

theorem histogram_equiv {A B C : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : A → C) (g : B → C) (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  have he := congrArg Finset.val (Finset.univ_map_equiv_to_embedding e)
  rw [Finset.map_val] at he
  calc
    _ = (Finset.univ.val.map e).map g := by
      rw [Multiset.map_map]
      congr 1
      funext a
      exact h a
    _ = _ := congrArg (Multiset.map g) he

noncomputable def neighborCount (W : Submodule F2 Mat3) (A : Mat3) (s t : Nat) : Nat :=
  Nat.card {B : W // B.val.rank = s ∧ (A + B.val).rank = t}

def codeNeighborCount (bs : List Nat) (a : Fin 512) (s t : Nat) : Nat :=
  ((spanEnum bs).filter fun b => rankCode b.val = s ∧ rankCode (xorCode a b).val = t).card

theorem codeNeighborCount_correct (bs : List Nat) (a : Fin 512) (s t : Nat) :
    codeNeighborCount bs a s t = neighborCount (spanCodes bs) (codeMat a.val) s t := by
  apply filter_card_eq_natCard (spanEnum bs) (spanEnumEquiv bs)
  intro b
  change (_ ∧ _) ↔ (codeMat b.val.val).rank = s ∧
    (codeMat a.val + codeMat b.val.val).rank = t
  rw [← codeMat_xor, rank_eq_rankCode_code, ← rank_eq_rankCode_code (xorCode a b)]
  rfl

theorem neighborCount_map (f : Mat3 →ₗ[F2] Mat3) (hf : Function.Injective f)
    (hr : ∀ M, (f M).rank = M.rank) (W : Submodule F2 Mat3) (A : Mat3) (s t : Nat) :
    neighborCount (W.map f) (f A) s t = neighborCount W A s t := by
  let e := (Submodule.equivMapOfInjective f hf W).toEquiv
  apply Eq.symm
  apply Nat.card_congr (e.subtypeEquiv (p := fun B : W => _)
    (q := fun B : W.map f => _) ?_)
  intro B
  change (B.val.rank = s ∧ (A + B.val).rank = t) ↔
    ((f B.val).rank = s ∧ (f A + f B.val).rank = t)
  rw [← map_add, hr, hr]

/-- A fixed base encodes the pointed rank counts; injectivity is not assumed. -/
def packProfile (r : Nat) (counts : Nat → Nat → Nat) : Nat :=
  r + 4 * (((List.range 4).flatMap fun s => (List.range 4).map (counts s)).foldr
    (fun n tail => n + 513 * tail) 0)

noncomputable def pointProfile (W : Submodule F2 Mat3) (A : Mat3) : Nat :=
  packProfile A.rank (neighborCount W A)

def codePointProfile (bs : List Nat) (a : Fin 512) : Nat :=
  packProfile (rankCode a.val) (codeNeighborCount bs a)

theorem codePointProfile_correct (bs : List Nat) (a : Fin 512) :
    codePointProfile bs a = pointProfile (spanCodes bs) (codeMat a.val) := by
  have h : codeNeighborCount bs a = neighborCount (spanCodes bs) (codeMat a.val) :=
    funext fun s => funext fun t => codeNeighborCount_correct bs a s t
  simp only [codePointProfile, pointProfile, h, rank_eq_rankCode_code]

theorem pointProfile_map (f : Mat3 →ₗ[F2] Mat3) (hf : Function.Injective f)
    (hr : ∀ M, (f M).rank = M.rank) (W : Submodule F2 Mat3) (A : Mat3) :
    pointProfile (W.map f) (f A) = pointProfile W A := by
  have h : neighborCount (W.map f) (f A) = neighborCount W A :=
    funext fun s => funext fun t => neighborCount_map f hf hr W A s t
  simp only [pointProfile, hr, h]

noncomputable def pointHistogram (W : Submodule F2 Mat3) : Multiset Nat := by
  classical
  exact (Finset.univ : Finset W).val.map (fun A => pointProfile W A.val)

def codePointHistogram (bs : List Nat) : Multiset Nat :=
  (spanEnum bs).val.map (codePointProfile bs)

/-- Structural recursion keeps closed finite certificates reducible in the kernel. -/
def kernelSort (s : Multiset Nat) : List Nat :=
  Quot.liftOn s (List.insertionSort (· ≤ ·)) fun a b h =>
    ((List.perm_insertionSort (· ≤ ·) a).trans
      (h.trans (List.perm_insertionSort (· ≤ ·) b).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort (· ≤ ·) a) (List.pairwise_insertionSort (· ≤ ·) b)

def pointSignature (bs : List Nat) : List Nat :=
  kernelSort (codePointHistogram bs)

theorem codePointHistogram_correct (bs : List Nat) :
    codePointHistogram bs = pointHistogram (spanCodes bs) := by
  classical
  have he := congrArg Finset.val (Finset.attach_map_val (s := spanEnum bs))
  rw [Finset.map_val, Finset.attach_eq_univ] at he
  unfold codePointHistogram pointHistogram
  rw [← he, Multiset.map_map]
  apply histogram_equiv (spanEnumEquiv bs)
  intro a
  exact codePointProfile_correct bs a.val

theorem pointHistogram_map (f : Mat3 →ₗ[F2] Mat3) (hf : Function.Injective f)
    (hr : ∀ M, (f M).rank = M.rank) (W : Submodule F2 Mat3) :
    pointHistogram (W.map f) = pointHistogram W := by
  classical
  apply Eq.symm
  apply histogram_equiv (Submodule.equivMapOfInjective f hf W).toEquiv
  intro A
  exact (pointProfile_map f hf hr W A.val).symm

theorem orbit_pointHistogram (i : Fin 496) (W : Submodule F2 Mat3)
    (h : frozenWangTable.OrbitImage i W) :
    pointHistogram W = codePointHistogram (frozenWangBasis i) := by
  obtain ⟨P, Q, ⟨hP⟩, ⟨hQ⟩, flip, rfl⟩ := h
  let := hP
  let := hQ
  have ha := pointHistogram_map (actionALinearMap P Q)
    (Function.LeftInverse.injective (pullbackA_actionA (P := P) (Q := Q)))
    (fun M => ah_action_rank_eq P Q M)
  have ht := pointHistogram_map transposeLinearMap Matrix.transpose_injective Matrix.rank_transpose
  rw [codePointHistogram_correct]
  cases flip with
  | false => exact ha _
  | true => exact (ha _).trans (ht _)

theorem pointSignature_eq_of_overlap (i j : Fin 496) (W : Submodule F2 Mat3)
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    pointSignature (frozenWangBasis i) = pointSignature (frozenWangBasis j) :=
  congrArg kernelSort
    ((orbit_pointHistogram i W hi).symm.trans (orbit_pointHistogram j W hj))

/-- Only equality preservation is used; no checksum injectivity is required. -/
def pointKey (bs : List Nat) : Nat :=
  (pointSignature bs).foldl (fun acc n => (acc * 65599 + n) % 1000000007) 0

theorem pointKey_eq_of_overlap (i j : Fin 496) (W : Submodule F2 Mat3)
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    pointKey (frozenWangBasis i) = pointKey (frozenWangBasis j) :=
  congrArg (fun ns : List Nat => ns.foldl (fun acc n => (acc * 65599 + n) % 1000000007) 0)
    (pointSignature_eq_of_overlap i j W hi hj)

end QiushiMatmul.FrozenLabel
