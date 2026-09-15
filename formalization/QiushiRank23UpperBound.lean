import QiushiDefs
import QiushiRank21Root

/-!
# A concrete rank-23 upper bound for binary 3×3 matrix multiplication

The coefficient triples below are the 23 terms in
`full_rank23_flipcpd_text_support.json`, interpreted as row-major nine-bit
matrix codes.  The full 729-coordinate tensor identity is checked by kernel
reduction; the JSON verifier is not trusted by this theorem.
-/

open Matrix BigOperators

namespace QiushiMatmul

def rank23ACode : Fin 23 → Nat := ![
  400, 260, 73, 393, 292, 8, 265, 146, 269, 72, 392, 144,
  284, 9, 256, 146, 448, 7, 32, 384, 268, 56, 16]

def rank23BCode : Fin 23 → Nat := ![
  304, 193, 7, 12, 448, 2, 72, 16, 65, 2, 260, 288,
  264, 67, 432, 40, 4, 8, 128, 52, 9, 256, 16]

def rank23CCode : Fin 23 → Nat := ![
  418, 10, 64, 68, 8, 210, 65, 2, 3, 192, 36, 390,
  12, 66, 130, 4, 320, 5, 24, 288, 9, 40, 432]

def rank23A (t : Fin 23) : Mat3 := codeMat (rank23ACode t)
def rank23B (t : Fin 23) : Mat3 := codeMat (rank23BCode t)
def rank23C (t : Fin 23) : Mat3 := codeMat (rank23CCode t)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 24000000 in
theorem rank23_entry_identity : ∀ a b c : Coord9,
    tensorEntry a b c = ∑ t : Fin 23,
      rank23A t a.1 a.2 * rank23B t b.1 b.2 * rank23C t c.1 c.2 := by
  decide +revert

def rank23Decomp : TensorEntryDecomp 23 where
  A := rank23A
  B := rank23B
  C := rank23C
  entry_identity := rank23_entry_identity

/-- Conservative upper-bound predicate for the canonical tensor.  Since zero
summands are allowed by `TensorEntryDecomp`, an exact `n`-term decomposition is
the usual assertion that tensor rank is at most `n`. -/
def TensorEntryRankAtMost (n : Nat) : Prop := Nonempty (TensorEntryDecomp n)

theorem rank_at_most_23 : TensorEntryRankAtMost 23 := ⟨rank23Decomp⟩

/-- Conditional interval theorem: the lower endpoint still consumes the
unchanged finite-premise record; the concrete upper endpoint is unconditional. -/
theorem rank_interval_21_23 (P : FinitePremises) :
    RankAtLeast 21 ∧ TensorEntryRankAtMost 23 :=
  ⟨rank_ge_21_of_premises P, rank_at_most_23⟩

end QiushiMatmul
