import QiushiCardinalityCNF

/-! Finite row enumeration, disjoint CNF composition, and occupation semantics. -/

namespace Qiushi.CNF
open Std.Sat BigOperators
noncomputable section

theorem prefix_fin_sum (x : Nat -> Bool) (n : Nat) :
    prefixCount x n = ∑ i : Fin n, bit (x i.val) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prefix_succ, Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last, ← ih] using
      (show prefixCount x n + (if x n then 1 else 0) = prefixCount x n + bit (x n) from rfl)

def enumerateSet {P : Type*} (s : Finset P) (i : Nat) : Option P :=
  if hi : i < s.card then some (s.equivFin.symm ⟨i,hi⟩) else none

def optionalValue {P : Type*} (a : P -> Bool) : Option P -> Bool
  | some p => a p
  | none => false

def setSignal {P : Type*} (a : P -> Bool) (s : Finset P) : Nat -> Bool :=
  optionalValue a ∘ enumerateSet s

theorem setSignal_count {P : Type*} (a : P -> Bool) (s : Finset P) :
    prefixCount (setSignal a s) s.card = ∑ p ∈ s, bit (a p) := by
  rw [prefix_fin_sum]
  calc
    _ = ∑ i : Fin s.card, bit (a (s.equivFin.symm i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [setSignal, enumerateSet, optionalValue, i.isLt]
    _ = ∑ p : s, bit (a p) := Fintype.sum_equiv s.equivFin.symm _ _ (fun _ => rfl)
    _ = ∑ p ∈ s, bit (a p) := Finset.sum_coe_sort s (fun p => bit (a p))

def finiteRowCNF {P : Type*} (s : Finset P) (cap : Int) (negated : Bool) :
    CNF (Sum (Option P) (Nat × Nat)) :=
  CNF.relabel (Sum.map (enumerateSet s) id)
    (if negated then flipPrimary (rowCNF s.card cap) else rowCNF s.card cap)

theorem sat_finiteRowCNF {P : Type*} (a : P -> Bool) (s : Finset P)
    (cap : Int) (negated : Bool) (y : Nat × Nat -> Bool) :
    CNF.Sat (Sum.elim (optionalValue a) y) (finiteRowCNF s cap negated) <->
    CNF.Sat (assign (setSignal a s) (fun i j => y (i,j)))
      (if negated then flipPrimary (rowCNF s.card cap) else rowCNF s.card cap) := by
  unfold finiteRowCNF CNF.Sat
  rw [CNF.eval_relabel]
  have he : (Sum.elim (optionalValue a) y) ∘ (Sum.map (enumerateSet s) id) =
      assign (setSignal a s) (fun i j => y (i,j)) := by
    funext v
    cases v <;> rfl
  rw [he]

theorem exists_uncurry (P : (Nat -> Nat -> Bool) -> Prop) :
    (exists y : Nat × Nat -> Bool, P (fun i j => y (i,j))) <-> exists y, P y := by
  constructor
  · rintro ⟨y,hy⟩; exact ⟨fun i j => y (i,j),hy⟩
  · rintro ⟨y,hy⟩; exact ⟨fun ij => y ij.1 ij.2,hy⟩

theorem finiteRowCNF_correct {P : Type*} (a : P -> Bool) (s : Finset P)
    (cap : Int) (negated : Bool) :
    (exists y, CNF.Sat (Sum.elim (optionalValue a) y) (finiteRowCNF s cap negated)) <->
      (if negated then (s.card : Int) - (∑ p ∈ s, bit (a p) : Nat)
        else (∑ p ∈ s, bit (a p) : Nat)) <= cap := by
  simp only [sat_finiteRowCNF]
  rw [exists_uncurry (fun y => CNF.Sat (assign (setSignal a s) y)
    (if negated then flipPrimary (rowCNF s.card cap) else rowCNF s.card cap))]
  cases negated with
  | false => simp [rowCNF_correct, setSignal_count]
  | true =>
    simp only [↓reduceIte, sat_flipPrimary, rowCNF_correct]
    have hc := prefix_complement (setSignal a s) s.card
    rw [setSignal_count] at hc
    omega

def systemRows {P : Type*} [Fintype P] {r : Nat}
    (rows : Fin r -> Finset P) (rhs : Fin r -> Int) (target : Nat) :
    Fin (r+2) -> CNF (Sum (Option P) (Nat × Nat)) :=
  Fin.cons (finiteRowCNF Finset.univ target false)
    (Fin.cons (finiteRowCNF Finset.univ ((Fintype.card P : Int) - target) true)
      (fun i => finiteRowCNF (rows i) (rhs i) false))

def booleanSystemCNF {P : Type*} [Fintype P] {r : Nat}
    (rows : Fin r -> Finset P) (rhs : Fin r -> Int) (target : Nat) :
    CNF (SharedVars (Option P) (fun _ : Fin (r+2) => Nat × Nat)) :=
  familyCNF (systemRows rows rhs target)

theorem booleanSystemCNF_correct {P : Type*} [Fintype P] {r : Nat}
    (rows : Fin r -> Finset P) (rhs : Fin r -> Int) (target : Nat) (a : P -> Bool) :
    (exists v,
      (forall p, v (.inl p) = optionalValue a p) ∧
      CNF.Sat v (booleanSystemCNF rows rhs target)) <->
    (∑ p, bit (a p)) = target ∧
      forall i, (∑ p ∈ rows i, (bit (a p) : Int)) <= rhs i := by
  rw [booleanSystemCNF, disjoint_extensions_iff]
  simp only [systemRows, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    finiteRowCNF_correct, Bool.false_eq_true, ↓reduceIte,
    Finset.card_univ, Nat.cast_sum]
  constructor
  · rintro ⟨hu,hl,hr⟩
    refine ⟨?_, hr⟩
    have hc : (∑ p, (bit (a p) : Int)) = ((∑ p, bit (a p) : Nat) : Int) := by simp
    omega
  · rintro ⟨he,hr⟩
    have hc : (∑ p, (bit (a p) : Int)) = ((∑ p, bit (a p) : Nat) : Int) := by simp
    exact ⟨by omega, by omega, hr⟩

abbrev CopyVar {Q : Type*} (cap : Q -> Nat) := (q : Q) × Fin (cap q)

def copyValue {Q : Type*} {cap : Q -> Nat} (y : Copies cap) (p : CopyVar cap) : Bool :=
  y p.1 p.2

def expandedRows {Q : Type*} (cap : Q -> Nat) {r : Nat}
    (rows : Fin r -> Finset Q) (i : Fin r) : Finset (CopyVar cap) :=
  (rows i).sigma (fun _q => Finset.univ)

theorem copy_total {Q : Type*} [Fintype Q] {cap : Q -> Nat} (y : Copies cap) :
    (∑ q, copyCount y q) = ∑ p, bit (copyValue y p) := by
  simp [copyCount, copyValue, Fintype.sum_sigma]

theorem copy_row_int {Q : Type*} [DecidableEq Q] {cap : Q -> Nat}
    (row : Finset Q) (y : Copies cap) :
    (∑ q ∈ row, (copyCount y q : Int)) =
      ∑ p ∈ row.sigma (fun _q => Finset.univ), (bit (copyValue y p) : Int) := by
  have h := row_sum_copies row y
  exact_mod_cast h

theorem copy_occupation {Q : Type*} [Fintype Q] [DecidableEq Q] {cap : Q -> Nat}
    {r : Nat} (rows : Fin r -> Finset Q) (rhs : Fin r -> Int) (target : Nat)
    (y : Copies cap) :
    Occupation rows rhs target (copyCount y) <->
      (∑ p, bit (copyValue y p)) = target ∧
        forall i, (∑ p ∈ expandedRows cap rows i, (bit (copyValue y p) : Int)) <= rhs i := by
  unfold Occupation
  rw [copy_total]
  simp only [copy_row_int, expandedRows]

/-- The extra fixed-false dummy handles empty finite input sets uniformly. -/
def occupationCNF {Q : Type*} [Fintype Q] (cap : Q -> Nat) {r : Nat}
    (rows : Fin r -> Finset Q) (rhs : Fin r -> Int) (target : Nat) :
    CNF (SharedVars (Option (CopyVar cap)) (fun _ : Fin (r+2) => Nat × Nat)) :=
  (booleanSystemCNF (expandedRows cap rows) rhs target).add [(.inl none, false)]

theorem sat_occupationCNF {Q : Type*} [Fintype Q] (cap : Q -> Nat) {r : Nat}
    (rows : Fin r -> Finset Q) (rhs : Fin r -> Int) (target : Nat) (v) :
    CNF.Sat v (occupationCNF cap rows rhs target) <->
      v (.inl none) = false ∧
      CNF.Sat v (booleanSystemCNF (expandedRows cap rows) rhs target) := by
  simp [occupationCNF, CNF.Sat, CNF.Clause.eval]

theorem occupationCNF_for_copies {Q : Type*} [Fintype Q] [DecidableEq Q]
    (cap : Q -> Nat) {r : Nat} (rows : Fin r -> Finset Q)
    (rhs : Fin r -> Int) (target : Nat) (y : Copies cap) :
    (exists v, (forall q j, v (.inl (some ⟨q,j⟩)) = y q j) ∧
      CNF.Sat v (occupationCNF cap rows rhs target)) <->
      Occupation rows rhs target (copyCount y) := by
  rw [copy_occupation]
  rw [← booleanSystemCNF_correct (expandedRows cap rows) rhs target (copyValue y)]
  constructor
  · rintro ⟨v,hy,hv⟩
    rcases (sat_occupationCNF cap rows rhs target v).mp hv with ⟨hn,hs⟩
    refine ⟨v, ?_, hs⟩
    intro p
    cases p with
    | none => exact hn
    | some p => exact hy p.1 p.2
  · rintro ⟨v,hv,hs⟩
    refine ⟨v, fun q j => hv (some ⟨q,j⟩), ?_⟩
    exact (sat_occupationCNF cap rows rhs target v).mpr ⟨hv none,hs⟩

/-- Unconditional equisatisfiability with a concrete, disjoint counter CNF. -/
theorem occupation_cnf_equisatisfiable {Q : Type*} [Fintype Q] [DecidableEq Q]
    (cap : Q -> Nat) {r : Nat} (rows : Fin r -> Finset Q)
    (rhs : Fin r -> Int) (target : Nat) :
    (exists x : Q -> Nat, (forall q, x q <= cap q) ∧ Occupation rows rhs target x) <->
      exists v, CNF.Sat v (occupationCNF cap rows rhs target) := by
  rw [occupation_iff_copies]
  constructor
  · rintro ⟨y,hy⟩
    rcases (occupationCNF_for_copies cap rows rhs target y).mpr hy with ⟨v,_,hv⟩
    exact ⟨v,hv⟩
  · rintro ⟨v,hv⟩
    let y : Copies cap := fun q j => v (.inl (some ⟨q,j⟩))
    exact ⟨y,(occupationCNF_for_copies cap rows rhs target y).mp
      ⟨v,fun _ _ => rfl,hv⟩⟩

theorem occupation_count_le_total {Q R : Type*} [Fintype Q]
    {rows : R -> Finset Q} {rhs : R -> Int} {target : Nat} {x : Q -> Nat}
    (h : Occupation rows rhs target x) (q : Q) : x q <= target := by
  have he : x q <= ∑ p, x p := Finset.single_le_sum (fun p _ => Nat.zero_le (x p))
    (Finset.mem_univ q)
  rwa [h.1] at he

/-- A selected strongest singleton cap is either the initial target or a row bound. -/
def SingletonCapSource {Q R : Type*} [DecidableEq Q] (rows : R -> Finset Q)
    (rhs : R -> Int) (target : Nat) (cap : Q -> Int) : Prop :=
  forall q, cap q = (target : Int) ∨ exists i, rows i = {q} ∧ rhs i = cap q

def clippedCaps {Q : Type*} (cap : Q -> Int) (target : Nat) (q : Q) : Nat :=
  (min (cap q) (target : Int)).toNat

theorem singleton_caps_entailed {Q R : Type*} [Fintype Q] [DecidableEq Q]
    {rows : R -> Finset Q} {rhs : R -> Int} {target : Nat} {cap : Q -> Int}
    (hs : SingletonCapSource rows rhs target cap) {x : Q -> Nat}
    (h : Occupation rows rhs target x) (q : Q) : x q <= clippedCaps cap target q := by
  have ht : (x q : Int) <= target := Nat.cast_le.mpr (occupation_count_le_total h q)
  have hc : (x q : Int) <= cap q := by
    rcases hs q with he | ⟨i,hi,hb⟩
    · rwa [he]
    · have hr := h.2 i
      simpa [hi, hb] using hr
  have hn := Int.toNat_le_toNat (le_min hc ht)
  simpa [clippedCaps] using hn

/-- The source encoder's cap selection/clipping loses no legal occupation vector. -/
theorem singleton_occupation_cnf_equisatisfiable {Q : Type*} [Fintype Q] [DecidableEq Q]
    {r : Nat} (rows : Fin r -> Finset Q) (rhs : Fin r -> Int) (target : Nat)
    (cap : Q -> Int) (hs : SingletonCapSource rows rhs target cap) :
    (exists x : Q -> Nat, Occupation rows rhs target x) <->
      exists v, CNF.Sat v (occupationCNF (clippedCaps cap target) rows rhs target) := by
  rw [← occupation_cnf_equisatisfiable]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,singleton_caps_entailed hs hx,hx⟩
  · rintro ⟨x,_,hx⟩
    exact ⟨x,hx⟩

end
end Qiushi.CNF
