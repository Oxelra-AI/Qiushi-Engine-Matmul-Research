import QiushiDefs

/-!
# Hua pairwise rank-one-difference fact over F₂

This bitmask layer is deliberately computational.  It supplies the finite kernel
fact for the Hua/affine-coset argument: two distinct rank-one `3×3` F₂ matrices
whose sum has rank at most one share a left or right outer-product factor.
-/

open BigOperators

namespace QiushiMatmul

/-- Row `i` of a 3×3 matrix encoded as a 9-bit natural number. -/
def rowBits (code : Nat) (i : Fin 3) : Nat :=
  (code >>> (3 * i.val)) &&& 7

/-- Minor determinant over F₂ for rows r1, r2 and columns c1, c2. -/
def minor2x2 (code : Nat) (r1 r2 c1 c2 : Fin 3) : Nat :=
  let a := (code >>> (3 * r1.val + c1.val)) &&& 1
  let b := (code >>> (3 * r1.val + c2.val)) &&& 1
  let c := (code >>> (3 * r2.val + c1.val)) &&& 1
  let d := (code >>> (3 * r2.val + c2.val)) &&& 1
  (a * d + b * c) % 2

/-- Boolean: has any nonzero 2×2 minor. -/
def hasRank2Minor (code : Nat) : Bool :=
  minor2x2 code 0 1 0 1 != 0 || minor2x2 code 0 1 0 2 != 0 ||
  minor2x2 code 0 1 1 2 != 0 || minor2x2 code 0 2 0 1 != 0 ||
  minor2x2 code 0 2 0 2 != 0 || minor2x2 code 0 2 1 2 != 0 ||
  minor2x2 code 1 2 0 1 != 0 || minor2x2 code 1 2 0 2 != 0 ||
  minor2x2 code 1 2 1 2 != 0

/-- The 3×3 determinant over F₂. -/
def det3x3 (code : Nat) : Nat :=
  let get (r c : Nat) := (code >>> (3 * r + c)) &&& 1
  (get 0 0 * (get 1 1 * get 2 2 + get 1 2 * get 2 1) +
   get 0 1 * (get 1 0 * get 2 2 + get 1 2 * get 2 0) +
   get 0 2 * (get 1 0 * get 2 1 + get 1 1 * get 2 0)) % 2

/-- Rank of a 3×3 F₂ matrix from its 9-bit code. -/
def rankCode (code : Nat) : Nat :=
  if code &&& 511 = 0 then 0
  else if !hasRank2Minor (code &&& 511) then 1
  else if det3x3 (code &&& 511) = 0 then 2
  else 3

/-- Bit `j` of a 3-bit vector. -/
def bitAt (v : Nat) (j : Fin 3) : Nat := (v >>> j.val) &&& 1

/-- Bitmask code of the outer product `u · vᵀ` for nonzero 3-bit vectors. -/
def outerCode (u v : Fin 7) : Nat :=
  let u' := u.val + 1
  let v' := v.val + 1
  (bitAt u' 0 * bitAt v' 0) * 1 +
  (bitAt u' 0 * bitAt v' 1) * 2 +
  (bitAt u' 0 * bitAt v' 2) * 4 +
  (bitAt u' 1 * bitAt v' 0) * 8 +
  (bitAt u' 1 * bitAt v' 1) * 16 +
  (bitAt u' 1 * bitAt v' 2) * 32 +
  (bitAt u' 2 * bitAt v' 0) * 64 +
  (bitAt u' 2 * bitAt v' 1) * 128 +
  (bitAt u' 2 * bitAt v' 2) * 256

/-- All encoded nonzero outer products are rank one. -/
theorem outerCode_rank_one (u v : Fin 7) : rankCode (outerCode u v) = 1 := by
  decide +revert

/-- The chosen nonzero-vector outer-product parametrization is injective over F₂. -/
theorem outerCode_injective (u1 v1 u2 v2 : Fin 7)
    (h : outerCode u1 v1 = outerCode u2 v2) : u1 = u2 ∧ v1 = v2 := by
  decide +revert

/-- **Hua pairwise kernel fact.** For two distinct rank-one `3×3` F₂ matrices,
if their XOR has rank at most one, then they share a left or right factor. -/
theorem hua_pairwise_rank_one (u1 v1 u2 v2 : Fin 7)
    (hne : outerCode u1 v1 ≠ outerCode u2 v2)
    (hsum : rankCode (Nat.xor (outerCode u1 v1) (outerCode u2 v2)) ≤ 1) :
    u1 = u2 ∨ v1 = v2 := by
  decide +revert

/-- The outer product `u · vᵀ` for 3-component F₂ vectors. -/
def outerMat (u v : I3 → F2) : Mat3 := fun i j => u i * v j

end QiushiMatmul
