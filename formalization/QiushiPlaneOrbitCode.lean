import QiushiAllHighPlaneGeometry

/-! Canonical two-dimensional matrix subspaces, without any counting premise. -/

open Matrix
namespace QiushiMatmul.PlaneOrbit
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

abbrev Space := Submodule F2 Mat3

def plane (a b : Nat) : Space :=
  Submodule.span F2 ({codeMat a, codeMat b} : Set Mat3)

def Valid (a b : Nat) : Prop :=
  a < 512 ∧ b < 512 ∧ 0 < a ∧ a < b ∧ b < Nat.xor a b

instance (a b : Nat) : Decidable (Valid a b) := inferInstanceAs (Decidable (_ ∧ _))

theorem encode_decode : ∀ c : Fin 512, matrixCodeNat (codeMat c.val) = c.val := by
  decide +revert

theorem code_injective {a b : Nat} (ha : a < 512) (hb : b < 512)
    (h : codeMat a = codeMat b) : a = b := by
  simpa only [encode_decode ⟨a, ha⟩, encode_decode ⟨b, hb⟩] using
    congrArg matrixCodeNat h

theorem scalar_cases (c : F2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem mem_plane (a b : Nat) (M : Mat3) :
    M ∈ plane a b ↔ M = 0 ∨ M = codeMat a ∨ M = codeMat b ∨
      M = codeMat (Nat.xor a b) := by
  rw [plane, Submodule.mem_span_pair, codeMat_xor]
  constructor
  · rintro ⟨r, s, h⟩
    rcases scalar_cases r with rfl | rfl <;>
      rcases scalar_cases s with rfl | rfl <;>
      simp_all [eq_comm]
  · rintro (h | h | h | h)
    · exact ⟨0, 0, by simp [h]⟩
    · exact ⟨1, 0, by simp [h]⟩
    · exact ⟨0, 1, by simp [h]⟩
    · exact ⟨1, 1, by simp [h]⟩

theorem xor_bound {a b : Nat} (ha : a < 512) (hb : b < 512) :
    Nat.xor a b < 512 := Nat.xor_lt_two_pow (n := 9) ha hb

theorem code_mem_plane {a b c : Nat} (ha : a < 512) (hb : b < 512)
    (hc : c < 512) : codeMat c ∈ plane a b ↔
      c = 0 ∨ c = a ∨ c = b ∨ c = Nat.xor a b := by
  rw [mem_plane, ← codeMat_zero]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (code_injective hc (by decide) h)
    · exact Or.inr (Or.inl (code_injective hc ha h))
    · exact Or.inr (Or.inr (Or.inl (code_injective hc hb h)))
    · exact Or.inr (Or.inr (Or.inr (code_injective hc (xor_bound ha hb) h)))
  · rintro (rfl | rfl | rfl | rfl) <;> simp

theorem plane_injective {a b c d : Nat} (hab : Valid a b) (hcd : Valid c d)
    (h : plane a b = plane c d) : a = c ∧ b = d := by
  obtain ⟨ha, hb, ha0, hab, hbx⟩ := hab
  obtain ⟨hc, hd, hc0, hcd, hdx⟩ := hcd
  have hmem (x y : Nat) : codeMat x ∈ plane x y :=
    Submodule.subset_span (by simp)
  have hmem' (x y : Nat) : codeMat y ∈ plane x y :=
    Submodule.subset_span (by simp)
  have hac := (code_mem_plane hc hd ha).mp (h ▸ hmem a b)
  have hca := (code_mem_plane ha hb hc).mp (h ▸ hmem c d)
  have hbd := (code_mem_plane hc hd hb).mp (h ▸ hmem' a b)
  have hdb := (code_mem_plane ha hb hd).mp (h ▸ hmem' c d)
  constructor <;> omega

theorem plane_finrank {a b : Nat} (h : Valid a b) :
    Module.finrank F2 (plane a b) = 2 := by
  have ha0 := h.2.2.1
  have hab0 := h.2.2.2.1
  have ha : codeMat a ≠ 0 := by
    intro hz
    have := code_injective h.1 (by decide) (hz.trans codeMat_zero.symm)
    omega
  have hb : codeMat b ≠ 0 := by
    intro hz
    have := code_injective h.2.1 (by decide) (hz.trans codeMat_zero.symm)
    omega
  have hab : codeMat a ≠ codeMat b := by
    intro he
    have := code_injective h.1 h.2.1 he
    omega
  have hi : LinearIndependent F2 (![codeMat a, codeMat b] : Fin 2 → Mat3) := by
    rw [linearIndependent_fin2]
    refine ⟨hb, ?_⟩
    intro c
    rcases scalar_cases c with rfl | rfl
    · simpa using ha.symm
    · simpa using hab.symm
  have hr : Set.range (![codeMat a, codeMat b] : Fin 2 → Mat3) =
      ({codeMat a, codeMat b} : Set Mat3) := by
    ext M
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hd := finrank_span_eq_card hi
  change Module.finrank F2 (Submodule.span F2
    (Set.range (![codeMat a, codeMat b] : Fin 2 → Mat3))) = 2 at hd
  rw [hr] at hd
  exact hd

end QiushiMatmul.PlaneOrbit
