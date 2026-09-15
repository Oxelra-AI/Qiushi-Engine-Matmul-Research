import QiushiGlobalOrbitCertificate
import QiushiGlobalOrbitExtension

/-! XOR-linear quotient normalization and small transition certificates. -/
namespace QiushiMatmul.GlobalOrbit
open PlaneOrbit
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def reduceCode : List Nat → Nat → Nat
  | [], c => c
  | b :: bs, c => reduceCode bs (if c.testBit b.log2 then c ^^^ b else c)

def packCode : List Nat → Nat → Nat
  | [], _ => 0
  | p :: ps, c => (if c.testBit p then 1 else 0) ^^^ (packCode ps c <<< 1)

def unpackCode : List Nat → Nat → Nat
  | [], _ => 0
  | p :: ps, c => (if c.testBit 0 then 2 ^ p else 0) ^^^ unpackCode ps (c >>> 1)

abbrev XorLinear (f : Nat → Nat) : Prop := ∀ a b, f (a ^^^ b) = f a ^^^ f b

theorem xorLinear_zero {f : Nat → Nat} (h : XorLinear f) : f 0 = 0 := by
  have he := h 0 0
  simpa using he

theorem conditional_xor (p b a c : Nat) :
    (if (a ^^^ c).testBit p then (a ^^^ c) ^^^ b else a ^^^ c) =
      (if a.testBit p then a ^^^ b else a) ^^^ (if c.testBit p then c ^^^ b else c) := by
  rw [Nat.testBit_xor]
  cases a.testBit p <;> cases c.testBit p <;> simp
  · ac_rfl
  · ac_rfl
  · calc
      a ^^^ c = (a ^^^ c) ^^^ (b ^^^ b) := by simp
      _ = _ := by ac_rfl

theorem xor_indicator (a b : Bool) (n : Nat) :
    (if a ^^ b then n else 0) = (if a then n else 0) ^^^ (if b then n else 0) := by
  cases a <;> cases b <;> simp

theorem reduceCode_linear (bs : List Nat) : XorLinear (reduceCode bs) := by
  induction bs with
  | nil => intro a b; rfl
  | cons x xs ih =>
    intro a b
    simp only [reduceCode, conditional_xor, ih]

theorem packCode_linear (ps : List Nat) : XorLinear (packCode ps) := by
  induction ps with
  | nil => intro a b; simp [packCode]
  | cons p ps ih =>
    intro a b
    simp only [packCode, Nat.testBit_xor, ih, Nat.shiftLeft_xor_distrib, xor_indicator]
    ac_rfl

theorem unpackCode_linear (ps : List Nat) : XorLinear (unpackCode ps) := by
  induction ps with
  | nil => intro a b; simp [unpackCode]
  | cons p ps ih =>
    intro a b
    simp only [unpackCode, Nat.testBit_xor, Nat.shiftRight_xor_distrib, ih, xor_indicator]
    ac_rfl

theorem packCode_bound (ps : List Nat) (c : Nat) : packCode ps c < 2 ^ ps.length := by
  induction ps with
  | nil => simp [packCode]
  | cons p ps ih =>
    change ((if c.testBit p then 1 else 0) ^^^ (packCode ps c <<< 1)) < 2 ^ (ps.length + 1)
    apply Nat.xor_lt_two_pow
    · split
      · have hp : 0 < 2 ^ ps.length := by positivity
        rw [Nat.pow_succ]
        omega
      · positivity
    · simpa only [Nat.shiftLeft_eq, Nat.pow_one, List.length_cons, Nat.pow_succ] using
        Nat.mul_lt_mul_of_pos_right ih (by decide : 0 < 2)

def coordinateCodes : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256]

theorem coordinate_expansion : ∀ c : Fin 512, xorSelected coordinateCodes c.val = c.val := by
  decide +kernel +revert

theorem xorLinear_ext_selected {f g : Nat → Nat} (hf : XorLinear f) (hg : XorLinear g)
    (bs : List Nat) (he : ∀ a ∈ bs, f a = g a) (mask : Nat) :
    f (xorSelected bs mask) = g (xorSelected bs mask) := by
  induction bs generalizing mask with
  | nil => simp only [xorSelected, xorLinear_zero hf, xorLinear_zero hg]
  | cons b bs ih =>
    change f ((if mask.testBit 0 then b else 0) ^^^ xorSelected bs (mask / 2)) =
      g ((if mask.testBit 0 then b else 0) ^^^ xorSelected bs (mask / 2))
    rw [hf, hg]
    congr 1
    · split
      · exact he b (by simp)
      · rw [xorLinear_zero hf, xorLinear_zero hg]
    · exact ih (fun a ha => he a (by simp [ha])) _

def NormalizationCheck (bs ps : List Nat) : Prop :=
  ∀ a ∈ coordinateCodes, unpackCode ps (packCode ps (reduceCode bs a)) = reduceCode bs a

instance (bs ps : List Nat) : Decidable (NormalizationCheck bs ps) :=
  inferInstanceAs (Decidable (∀ a ∈ coordinateCodes,
    unpackCode ps (packCode ps (reduceCode bs a)) = reduceCode bs a))

theorem normalization_sound (bs ps : List Nat) (h : NormalizationCheck bs ps) (c : Fin 512) :
    unpackCode ps (packCode ps (reduceCode bs c.val)) = reduceCode bs c.val := by
  have hf : XorLinear (fun a => unpackCode ps (packCode ps (reduceCode bs a))) := by
    intro a b
    change unpackCode ps (packCode ps (reduceCode bs (a ^^^ b))) = _
    rw [reduceCode_linear bs a b, packCode_linear ps _ _, unpackCode_linear ps _ _]
  have he := xorLinear_ext_selected hf (reduceCode_linear bs) coordinateCodes h c.val
  rwa [coordinate_expansion c] at he

theorem extend_add_mem (W : Space) (X Y : Mat3) (hY : Y ∈ W) :
    extend W (X + Y) = extend W X := by
  have hle (A B : Mat3) (hB : B ∈ W) : extend W (A + B) ≤ extend W A := by
    apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro M rfl
    have hA : A ∈ extend W A :=
      (show Submodule.span F2 {A} ≤ extend W A from le_sup_right) (Submodule.subset_span (by simp))
    have hB' : B ∈ extend W A := (show W ≤ extend W A from le_sup_left) hB
    exact (extend W A).add_mem hA hB'
  apply le_antisymm (hle X Y hY)
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using hle (X + Y) Y hY

theorem reduceCode_extension (W : Space) (bs : List Nat)
    (hb : ∀ b ∈ bs, codeMat b ∈ W) (c : Nat) :
    extend W (codeMat c) = extend W (codeMat (reduceCode bs c)) := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    simp only [reduceCode]
    split
    · calc
        _ = extend W (codeMat (c ^^^ b)) := by
          change extend W (codeMat c) = extend W (codeMat (Nat.xor c b))
          rw [codeMat_xor, extend_add_mem W _ _ (hb b (by simp))]
        _ = _ := ih (fun a ha => hb a (by simp [ha])) _
    · exact ih (fun a ha => hb a (by simp [ha])) _

def SpanCheck (bs cs forward backward : List Nat) : Prop :=
  (∀ i : Fin bs.length, xorSelected cs (forward.getD i.val 0) = bs[i.val]) ∧
  (∀ i : Fin cs.length, xorSelected bs (backward.getD i.val 0) = cs[i.val])

instance (bs cs forward backward : List Nat) : Decidable (SpanCheck bs cs forward backward) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem spanCheck_sound (bs cs f b : List Nat) (h : SpanCheck bs cs f b) :
    spanCodes bs = spanCodes cs := by
  have hle (xs ys ms : List Nat)
      (hm : ∀ i : Fin xs.length, xorSelected ys (ms.getD i.val 0) = xs[i.val]) :
      spanCodes xs ≤ spanCodes ys := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [← hm ⟨i, hi⟩]
    exact codeMat_xorSelected_mem_spanCodes ys _
  exact le_antisymm (hle bs cs f h.1) (hle cs bs b h.2)

structure Transition where
  target : Fin 496
  word : List (Fin 4)
  forward : List Nat
  backward : List Nat

def TransitionCheck (i : Fin 496) (c : Nat) (t : Transition) : Prop :=
  SpanCheck (c :: frozenWangBasis i)
    ((frozenWangBasis t.target).map (wordCode t.word)) t.forward t.backward

instance (i : Fin 496) (c : Nat) (t : Transition) : Decidable (TransitionCheck i c t) :=
  inferInstanceAs (Decidable (SpanCheck _ _ _ _))

theorem frozen_codes_bounded : ∀ i : Fin 496, ∀ c ∈ frozenWangBasis i, c < 512 := by
  decide +kernel +revert

theorem transition_sound (i : Fin 496) (c : Nat) (t : Transition) (h : TransitionCheck i c t) :
    Covered (spanCodes (c :: frozenWangBasis i)) := by
  refine ⟨t.target, (frozen_image_iff _ _).mpr ?_⟩
  rw [spanCheck_sound _ _ _ _ h, word_spanCodes _ _ (frozen_codes_bounded t.target)]
  exact wordSpace_equivalent _ _

theorem extensions_of_normalized (i : Fin 496) (ps : List Nat)
    (hn : NormalizationCheck (frozenWangBasis i) ps)
    (rows : Fin (2 ^ ps.length) → Transition)
    (hr : ∀ k, TransitionCheck i (unpackCode ps k.val) (rows k)) :
    ∀ c : Fin 512, Covered (spanCodes (c.val :: frozenWangBasis i)) := by
  intro c
  let k : Fin (2 ^ ps.length) := ⟨packCode ps (reduceCode (frozenWangBasis i) c.val),
    packCode_bound _ _⟩
  have ht := transition_sound i (unpackCode ps k.val) (rows k) (hr k)
  rw [spanCodes_cons] at ht ⊢
  have he := reduceCode_extension (spanCodes (frozenWangBasis i)) (frozenWangBasis i)
    (fun b hb => Submodule.subset_span ⟨b, hb, rfl⟩) c.val
  rw [he]
  have hn' := normalization_sound _ _ hn c
  change unpackCode ps k.val = reduceCode (frozenWangBasis i) c.val at hn'
  rwa [hn'] at ht

end QiushiMatmul.GlobalOrbit
