import QiushiFrozenLabelKeysData
import Mathlib.Tactic.Eval

namespace QiushiMatmul.FrozenLabel

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private abbrev SignatureRow := Nat × (Nat × Nat) × Nat

private def signatureRowKey (r : SignatureRow) : Nat := Nat.pair r.2.1.1 r.2.1.2

private def rowsSeparated (a b : SignatureRow) : Prop :=
  a.2.1 ≠ b.2.1 ∨ a.2.2 = b.2.2 ∨ (min a.1 b.1, max a.1 b.1) ∈ collisionPairs

-- This produces data only. The checks below bind every row to the original fixture.
private def signatureGroups : List (Nat × List SignatureRow) := eval%
  let rows := List.ofFn (fun i : Fin 496 => (i.val, signatureFixture i, frozenWangLower i))
  let keys := ((rows.map signatureRowKey).mergeSort (fun a b => decide (a ≤ b))).eraseDups
  keys.map fun k => (k, rows.filter fun r => signatureRowKey r == k)

private theorem signatureGroups_complete :
    (signatureGroups.flatMap Prod.snd).insertionSort (fun a b => a.1 ≤ b.1) =
      List.ofFn (fun i : Fin 496 => (i.val, signatureFixture i, frozenWangLower i)) := by
  decide +kernel

private theorem signatureGroups_keys : ∀ g ∈ signatureGroups, ∀ r ∈ g.2,
    signatureRowKey r = g.1 := by decide +kernel

private theorem signatureGroups_increasing :
    (signatureGroups.map Prod.fst).IsChain (· < ·) := by decide +kernel

private theorem signatureGroups_internal : ∀ g ∈ signatureGroups,
    g.2.Pairwise rowsSeparated := by
  unfold rowsSeparated
  decide +kernel

private theorem rowsSeparated_symm {a b : SignatureRow} (h : rowsSeparated a b) :
    rowsSeparated b a := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (by simpa only [Nat.min_comm, Nat.max_comm] using h))

private theorem signatureGroups_pairwise :
    (signatureGroups.flatMap Prod.snd).Pairwise rowsSeparated := by
  apply List.pairwise_flatMap.mpr
  refine ⟨signatureGroups_internal, ?_⟩
  have hk := List.isChain_iff_pairwise.mp signatureGroups_increasing
  rw [List.pairwise_map] at hk
  apply List.Pairwise.imp_of_mem ?_ hk
  intro a b ha hb hab x hx y hy
  apply Or.inl
  intro he
  have he' := congrArg (fun s : Nat × Nat => Nat.pair s.1 s.2) he
  change signatureRowKey x = signatureRowKey y at he'
  rw [signatureGroups_keys a ha x hx, signatureGroups_keys b hb y hy] at he'
  exact (Nat.ne_of_lt hab) he'

theorem signatureFixture_separates : ∀ i j : Fin 496,
    i.val < j.val → signatureFixture i = signatureFixture j →
      frozenWangLower i = frozenWangLower j ∨ (i.val, j.val) ∈ collisionPairs := by
  intro i j hij heq
  have hp := (List.perm_insertionSort (fun (a b : SignatureRow) => a.1 ≤ b.1)
    (signatureGroups.flatMap Prod.snd)).symm
  rw [signatureGroups_complete] at hp
  have h := signatureGroups_pairwise.perm hp rowsSeparated_symm
  rw [List.pairwise_ofFn] at h
  have result := (h (i := i) (j := j) hij).resolve_left (not_not_intro heq)
  simpa only [Nat.min_eq_left (Nat.le_of_lt hij), Nat.max_eq_right (Nat.le_of_lt hij)] using result

end QiushiMatmul.FrozenLabel
