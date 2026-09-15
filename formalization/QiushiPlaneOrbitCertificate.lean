import QiushiPlaneOrbitAction

/-! A reusable finite graph certificate: closure, connectivity, and injective decoding. -/
open Matrix
namespace QiushiMatmul.PlaneOrbit
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def InThree (x a b : Nat) : Prop := x = a ∨ x = b ∨ x = Nat.xor a b
instance (x a b : Nat) : Decidable (InThree x a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

def ImageCheck (g : Fin 4) (a b c d : Nat) : Prop :=
  InThree (genCode g a) c d ∧ InThree (genCode g b) c d
instance (g : Fin 4) (a b c d : Nat) : Decidable (ImageCheck g a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

def genEquiv (g : Fin 4) : Mat3 ≃ₗ[F2] Mat3 :=
  { genMap g with
    invFun := genMap g
    left_inv := genMap_involution g
    right_inv := genMap_involution g }

theorem imageCheck_sound {g : Fin 4} {a b c d : Nat}
    (hab : Valid a b) (hcd : Valid c d) (h : ImageCheck g a b c d) :
    genW g (plane a b) = plane c d := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [genW, plane, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro M ⟨X, hX, rfl⟩
    rcases hX with rfl | ⟨rfl⟩
    · rw [← genCode_semantics g ⟨a, hab.1⟩]
      exact (code_mem_plane hcd.1 hcd.2.1 (genCode_bound g ⟨a, hab.1⟩)).mpr (Or.inr h.1)
    · rw [← genCode_semantics g ⟨b, hab.2.1⟩]
      exact (code_mem_plane hcd.1 hcd.2.1 (genCode_bound g ⟨b, hab.2.1⟩)).mpr (Or.inr h.2)
  · change Module.finrank F2 ((plane a b).map (genEquiv g).toLinearMap) = _
    rw [LinearEquiv.finrank_map_eq, plane_finrank hab, plane_finrank hcd]

structure OrbitRow where
  a : Nat
  b : Nat
  depth : Nat
  parent : Nat
  next0 : Nat
  next1 : Nat
  next2 : Nat
  next3 : Nat

def OrbitRow.next (r : OrbitRow) (g : Fin 4) : Nat :=
  match g.val with
  | 0 => r.next0
  | 1 => r.next1
  | 2 => r.next2
  | _ => r.next3

structure OrbitData (n : Nat) where
  rows : Fin (n + 1) → OrbitRow

namespace OrbitData
variable {n : Nat} (D : OrbitData n)

def ix (_ : OrbitData n) (i : Nat) : Fin (n + 1) := ⟨i % (n + 1), Nat.mod_lt _ (by omega)⟩
def row (i : Fin (n + 1)) : OrbitRow := D.rows i
def space (i : Fin (n + 1)) : Space := plane (D.row i).a (D.row i).b
def key (i : Fin (n + 1)) : Nat := (D.row i).a * 512 + (D.row i).b

def RowOK (i : Fin (n + 1)) : Prop :=
  Valid (D.row i).a (D.row i).b ∧
  (i.val < n → D.key i < D.key (D.ix (i.val + 1))) ∧
  (i = 0 ∨
    ((D.row (D.ix (D.row i).parent)).depth < (D.row i).depth ∧
      ∃ g : Fin 4, ImageCheck g
        (D.row (D.ix (D.row i).parent)).a (D.row (D.ix (D.row i).parent)).b
        (D.row i).a (D.row i).b)) ∧
  ∀ g : Fin 4, ImageCheck g (D.row i).a (D.row i).b
    (D.row (D.ix ((D.row i).next g))).a (D.row (D.ix ((D.row i).next g))).b

instance (i : Fin (n + 1)) : Decidable (D.RowOK i) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem of_blocks {k : Nat} [NeZero k]
    (h : ∀ b : Fin (n / k + 1), ∀ j : Fin k,
      D.RowOK (D.ix (b.val * k + j.val))) : ∀ i, D.RowOK i := by
  intro i
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  let b : Fin (n / k + 1) := ⟨i.val / k,
    Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ i.isLt))⟩
  let j : Fin k := ⟨i.val % k, Nat.mod_lt _ hk⟩
  have he : D.ix (b.val * k + j.val) = i := by
    apply Fin.ext
    change (i.val / k * k + i.val % k) % (n + 1) = i.val
    rw [Nat.mul_comm (i.val / k), Nat.div_add_mod, Nat.mod_eq_of_lt i.isLt]
  simpa only [he] using h b j

variable (hD : ∀ i, D.RowOK i)
include hD

theorem valid (i : Fin (n + 1)) : Valid (D.row i).a (D.row i).b := (hD i).1

theorem strictMono_key : StrictMono D.key := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have h := (hD i.castSucc).2.1 i.isLt
  have he : D.ix (i.castSucc.val + 1) = i.succ := by
    apply Fin.ext
    simp [ix]
  rwa [he] at h

theorem space_injective : Function.Injective D.space := by
  intro i j he
  obtain ⟨ha, hb⟩ := plane_injective (D.valid hD i) (D.valid hD j) he
  apply (D.strictMono_key hD).injective
  simp only [key, ha, hb]

theorem dimension (i : Fin (n + 1)) : Module.finrank F2 (D.space i) = 2 :=
  plane_finrank (D.valid hD i)

theorem closed : GeneratorClosed (Set.range D.space) := by
  rintro g W ⟨i, rfl⟩
  refine ⟨D.ix ((D.row i).next g), ?_⟩
  exact (imageCheck_sound (D.valid hD i) (D.valid hD _) ((hD i).2.2.2 g)).symm

theorem connected (i : Fin (n + 1)) : Equivalent (D.space 0) (D.space i) := by
  have aux : ∀ depth, ∀ j : Fin (n + 1), (D.row j).depth = depth →
      Equivalent (D.space 0) (D.space j) := by
    intro depth
    induction depth using Nat.strong_induction_on with
    | h depth ih =>
      intro j hj
      rcases (hD j).2.2.1 with rfl | ⟨hd, g, hg⟩
      · exact equivalent_refl _
      · have hp := ih (D.row (D.ix (D.row j).parent)).depth (by omega) _ rfl
        have he := imageCheck_sound (D.valid hD (D.ix (D.row j).parent)) (D.valid hD j) hg
        change genW g (D.space (D.ix (D.row j).parent)) = D.space j at he
        rw [← he]
        exact equivalent_trans hp (generator_equivalent g _)
  exact aux _ i rfl

/-- The certificate's range is exactly the genuine full-action orbit. -/
theorem orbit_exact (W : Space) :
    Equivalent (D.space 0) W ↔ W ∈ Set.range D.space := by
  constructor
  · intro h
    exact (equivalent_mem_iff (D.closed hD) h).mp ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    exact D.connected hD i

noncomputable def orbitEquiv : Fin (n + 1) ≃ {W : Space // Equivalent (D.space 0) W} :=
  Equiv.ofBijective (fun i => ⟨D.space i, D.connected hD i⟩) (by
    constructor
    · intro i j h
      exact D.space_injective hD (congrArg Subtype.val h)
    · rintro ⟨W, hW⟩
      obtain ⟨i, hi⟩ := (D.orbit_exact hD W).mp hW
      exact ⟨i, Subtype.ext hi⟩)

theorem orbit_card : Nat.card {W : Space // Equivalent (D.space 0) W} = n + 1 := by
  rw [← Nat.card_congr (D.orbitEquiv hD), Nat.card_fin]

theorem equivalent_root_keys {m : Nat} (E : OrbitData m) (hE : ∀ i, E.RowOK i)
    (h : Equivalent (D.space 0) (E.space 0)) : D.key 0 = E.key 0 := by
  obtain ⟨i, hi⟩ := (D.orbit_exact hD _).mp h
  obtain ⟨j, hj⟩ := (E.orbit_exact hE _).mp (equivalent_symm h)
  obtain ⟨ha, hb⟩ := plane_injective (D.valid hD i) (E.valid hE 0) hi
  obtain ⟨hc, hd⟩ := plane_injective (E.valid hE j) (D.valid hD 0) hj
  have h1 := (D.strictMono_key hD).monotone (Fin.zero_le i)
  have h2 := (E.strictMono_key hE).monotone (Fin.zero_le j)
  simp only [key, ha, hb, hc, hd] at h1 h2 ⊢
  omega

end OrbitData
end QiushiMatmul.PlaneOrbit
