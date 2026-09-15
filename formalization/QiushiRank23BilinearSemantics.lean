import QiushiBilinearSemantics
import QiushiRank23UpperBound

open Matrix BigOperators

namespace QiushiMatmul

/-- The already checked 23 coefficient triples multiply every pair of inputs. -/
theorem rank23_bilinear_algorithm (X Y : Mat3) :
    X * Y = bilinearAlgorithm rank23A rank23B rank23C X Y :=
  (tensorEntry_identity_iff_bilinearAlgorithm rank23A rank23B rank23C).mp
    rank23_entry_identity X Y

/-- The same 23-term algorithm using the existing linear-form interface. -/
theorem rank23_mul_eq (X Y : Mat3) :
    X * Y = ∑ t : Fin 23,
      (leftForm rank23Decomp t X * rightForm rank23Decomp t Y) • rank23C t :=
  rank23Decomp.mul_eq X Y

end QiushiMatmul
