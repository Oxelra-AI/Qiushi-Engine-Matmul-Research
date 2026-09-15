import QiushiMat3SubspaceCount
import QiushiRankBridge
import QiushiCodeSpanBridgeCore

open Matrix BigOperators
attribute [local instance] Classical.propDecidable Fintype.ofFinite

noncomputable section
namespace QiushiMatmul.AllHighCount

open E11SubspaceCount

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- The report's all-high condition on actual matrix subspaces. -/
def allHigh (W : Submodule F2 Mat3) : Prop :=
  ∀ A ∈ W, A ≠ 0 → 2 ≤ A.rank

def HighPair (A B : Mat3) : Prop :=
  2 ≤ A.rank ∧ 2 ≤ B.rank ∧ 2 ≤ (A + B).rank

abbrev HighPlanes := {W : Submodule F2 Mat3 // Module.finrank F2 W = 2 ∧ allHigh W}
abbrev HighSpaces := {S : Spaces Mat3 2 // allHigh S.val}
abbrev HighPairs := {p : Mat3 × Mat3 // HighPair p.1 p.2}

lemma high_ne_zero {A : Mat3} (h : 2 ≤ A.rank) : A ≠ 0 := by
  intro hA
  subst A
  simp at h

lemma scalar_cases (s : F2) : s = 0 ∨ s = 1 := by decide +revert

lemma highPair_independent {A B : Mat3} (h : HighPair A B) :
    LinearIndependent F2 ![A, B] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t hst
  rcases scalar_cases s with rfl | rfl <;>
    rcases scalar_cases t with rfl | rfl <;> simp_all [HighPair]

lemma allHigh_span_pair {A B : Mat3} (h : HighPair A B) :
    allHigh (Submodule.span F2 {A, B}) := by
  intro X hX hn
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hX
  rcases scalar_cases s with rfl | rfl <;>
    rcases scalar_cases t with rfl | rfl <;> simp_all [HighPair]

lemma highPair_of_allHigh (v : Independent Mat3 2)
    (h : allHigh (Submodule.span F2 (Set.range v.val))) : HighPair (v.val 0) (v.val 1) := by
  have h0 : v.val 0 ≠ 0 := v.property.ne_zero 0
  have h1 : v.val 1 ≠ 0 := v.property.ne_zero 1
  have hsum : v.val 0 + v.val 1 ≠ 0 := by
    intro heq
    have hlin := (Fintype.linearIndependent_iff.mp v.property) (fun _ => (1 : F2))
      (by simpa [Fin.sum_univ_two] using heq)
    have hh := hlin 0
    norm_num at hh
  exact ⟨h _ (Submodule.subset_span (Set.mem_range_self 0)) h0,
    h _ (Submodule.subset_span (Set.mem_range_self 1)) h1,
    h _ ((Submodule.span F2 (Set.range v.val)).add_mem
      (Submodule.subset_span (Set.mem_range_self 0))
      (Submodule.subset_span (Set.mem_range_self 1))) hsum⟩

/-- Restrict the existing frame equivalence, retaining the actual span. -/
def highFrameEquiv :
    (Σ S : HighSpaces, Independent S.val.val 2) ≃
      {v : Independent Mat3 2 // allHigh (Submodule.span F2 (Set.range v.val))} :=
  (Equiv.subtypeSigmaEquiv (fun S : Spaces Mat3 2 => Independent S.val 2)
    (fun S => allHigh S.val)).symm.trans
    ((frameEquiv Mat3 2).subtypeEquiv (by
      rintro ⟨S, v⟩
      change allHigh S.val ↔
        allHigh (Submodule.span F2 (Set.range (forgetFrame Mat3 ⟨S, v⟩).val))
      rw [span_forgetFrame]))

def highFramePairEquiv :
    {v : Independent Mat3 2 // allHigh (Submodule.span F2 (Set.range v.val))} ≃ HighPairs where
  toFun v := ⟨(v.val.val 0, v.val.val 1), highPair_of_allHigh v.val v.property⟩
  invFun p := ⟨⟨![p.val.1, p.val.2], highPair_independent p.property⟩,
    by simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using allHigh_span_pair p.property⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Every eligible ordered matrix pair is precisely an ordered basis of its all-high plane. -/
def highBasisEquiv : (Σ S : HighSpaces, Independent S.val.val 2) ≃ HighPairs :=
  highFrameEquiv.trans highFramePairEquiv

theorem highBasisEquiv_span (S : HighSpaces) (v : Independent S.val.val 2) :
    Submodule.span F2 {(highBasisEquiv ⟨S, v⟩).val.1,
      (highBasisEquiv ⟨S, v⟩).val.2} = S.val.val := by
  have hrange : Set.range (forgetFrame Mat3 ⟨S.val, v⟩).val =
      {(v.val 0 : Mat3), (v.val 1 : Mat3)} := by
    ext X
    simp [forgetFrame, Fin.exists_fin_two, eq_comm]
  have h := span_forgetFrame Mat3 S.val v
  rw [hrange] at h
  exact h

theorem high_plane_basis_count (S : HighSpaces) : Nat.card (Independent S.val.val 2) = 6 := by
  have h := card_linearIndependent (K := F2) (V := S.val.val) (k := 2)
    (by rw [S.val.property])
  simpa [Independent, F2, S.val.property, Fin.prod_univ_succ] using h

def highSpacesEquiv : HighSpaces ≃ HighPlanes :=
  Equiv.subtypeSubtypeEquivSubtypeInter
    (fun W : Submodule F2 Mat3 => Module.finrank F2 W = 2) allHigh

/-- Six-to-one counting for actual planes, independently of any orbit classification. -/
theorem high_pair_count_eq_six_mul_planes : Nat.card HighPairs = Nat.card HighPlanes * 6 := by
  calc
    Nat.card HighPairs = Nat.card (Σ S : HighSpaces, Independent S.val.val 2) :=
      (Nat.card_congr highBasisEquiv).symm
    _ = ∑ S : HighSpaces, Nat.card (Independent S.val.val 2) := Nat.card_sigma
    _ = Nat.card HighSpaces * 6 := by
      simp_rw [high_plane_basis_count]
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card HighPlanes * 6 := by rw [Nat.card_congr highSpacesEquiv]

end QiushiMatmul.AllHighCount
