import Mathlib
import QiushiDefs

/-!
# Orbit-agnostic code-level span bridge

**Purpose**: The single reusable bridge between compiled Boolean kernel checks
and abstract `Submodule` membership.  This eliminates the need for hundreds of
individual Mat3 subspace-membership proofs.

**Key theorem** (`spanContainsCode_implies_mem_spanCodes`):

    spanContainsCode basis n = true → codeMat n ∈ spanCodes basis

**Proof structure**:
1. `codeMat` maps `Nat.xor` to `+` over F₂ (group homomorphism).
2. `xorSelected basis mask` computes the XOR of selected basis elements.
3. Its `codeMat` image is a sum of generators → lies in `spanCodes basis`.
4. `spanContainsCode` witnesses the existence of such a mask.
5. `codeMat (n &&& 511) = codeMat n` (9-bit truncation is invisible).

This module contains no orbit-specific material.  Modules that need only the
generic bridge should import this directly; `QiushiCodeSpanBridge` remains as
a compatibility aggregate that adds orbit-486-specific convenience lemmas.
-/

set_option maxHeartbeats 800000
open BigOperators Finset
namespace QiushiMatmul

/-- XOR of the entries selected by the low bits of `mask`.
This was formerly owned by the orbit-486 quotient-label module; it is generic
bit-vector span infrastructure and belongs in the orbit-free bridge core. -/
def xorSelected : List Nat → Nat → Nat
  | [], _ => 0
  | b :: bs, mask => Nat.xor (if Nat.testBit mask 0 then b else 0) (xorSelected bs (mask / 2))

/-- Boolean span membership for row-major 9-bit matrix-code bases. -/
def spanContainsCode (basis : List Nat) (x : Nat) : Bool :=
  (List.range (2 ^ basis.length)).any (fun mask => decide (xorSelected basis mask = (x &&& 511)))

-- ============================================================================
-- Section 1: codeMat is a group homomorphism from (ℕ, xor) to (Mat3, +)
-- ============================================================================

/-- Bool XOR corresponds to F₂ addition on indicator values. -/
private lemma boolXor_ite_F2 (a b : Bool) :
    (if a ^^ b then (1 : F2) else 0) =
    (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> simp [CharTwo.add_self_eq_zero]

/-- `codeMat` maps `Nat.xor` to matrix addition over F₂.
    This is the key algebraic identity: XOR at the bit level becomes
    addition in the vector space `Mat3 = (ZMod 2)^{3×3}`. -/
theorem codeMat_xor (a b : Nat) : codeMat (Nat.xor a b) = codeMat a + codeMat b := by
  ext i j
  simp only [codeMat, Matrix.add_apply]
  change (if Nat.testBit (a ^^^ b) (3 * i.val + j.val) then (1 : F2) else 0) =
    (if Nat.testBit a (3 * i.val + j.val) then 1 else 0) +
    (if Nat.testBit b (3 * i.val + j.val) then 1 else 0)
  rw [Nat.testBit_xor]
  exact boolXor_ite_F2
    (Nat.testBit a (3 * i.val + j.val))
    (Nat.testBit b (3 * i.val + j.val))

/-- `codeMat 0 = 0`: the zero code maps to the zero matrix. -/
theorem codeMat_zero : codeMat 0 = (0 : Mat3) := by
  ext i j; simp [codeMat]

-- ============================================================================
-- Section 2: 9-bit truncation is invisible to codeMat
-- ============================================================================

/-- For 3×3 matrices, only bits 0–8 matter.  Masking with 511 = 2⁹-1 is
    the identity on the `codeMat` image. -/
theorem codeMat_and_511 (n : Nat) : codeMat (n &&& 511) = codeMat n := by
  ext i j
  simp only [codeMat]
  congr 1
  rw [Nat.testBit_and]
  have h511 : Nat.testBit 511 (3 * i.val + j.val) = true := by
    fin_cases i <;> fin_cases j <;> decide
  simp [h511]

-- ============================================================================
-- Section 3: xorSelected produces elements in spanCodes
-- ============================================================================

private lemma spanCodes_cons_le (b : Nat) (bs : List Nat) :
    spanCodes bs ≤ spanCodes (b :: bs) :=
  Submodule.span_mono (fun _ ⟨n, hn, hM⟩ => ⟨n, List.mem_cons_of_mem b hn, hM⟩)

/-- `codeMat(xorSelected basis mask) ∈ spanCodes basis`, for any mask.
    By induction: XOR splits into a generator term (or zero) plus
    the recursive result, both in the span. -/
theorem codeMat_xorSelected_mem_spanCodes (basis : List Nat) (mask : Nat) :
    codeMat (xorSelected basis mask) ∈ spanCodes basis := by
  induction basis generalizing mask with
  | nil =>
    simp only [xorSelected]
    rw [codeMat_zero]
    exact (spanCodes []).zero_mem
  | cons b bs ih =>
    -- Unfold one level: xorSelected (b :: bs) mask = xor (if testBit mask 0 then b else 0) (xorSelected bs (mask/2))
    show codeMat (Nat.xor (if Nat.testBit mask 0 then b else 0)
                           (xorSelected bs (mask / 2))) ∈ _
    rw [codeMat_xor]
    apply (spanCodes (b :: bs)).add_mem
    · -- First summand: codeMat (if testBit mask 0 then b else 0)
      -- Split on the Bool condition
      split
      · -- true: codeMat b ∈ spanCodes (b :: bs)
        exact Submodule.subset_span ⟨b, by simp, rfl⟩
      · -- false: codeMat 0 ∈ spanCodes (b :: bs)
        rw [codeMat_zero]
        exact (spanCodes (b :: bs)).zero_mem
    · -- Second summand: by IH and monotonicity
      exact spanCodes_cons_le b bs (ih (mask / 2))

-- ============================================================================
-- Section 4: The bridge theorem
-- ============================================================================

/-- **The bridge theorem**: if `spanContainsCode basis n = true` (a Boolean
    kernel check), then `codeMat n ∈ spanCodes basis` (abstract submodule
    membership).  This is the only proof needed to connect all compiled
    finite occupation certificates to the quotient geometry. -/
theorem spanContainsCode_implies_mem_spanCodes (basis : List Nat) (n : Nat)
    (h : spanContainsCode basis n = true) :
    codeMat n ∈ spanCodes basis := by
  simp only [spanContainsCode, List.any_eq_true, List.mem_range,
             decide_eq_true_eq] at h
  obtain ⟨mask, _, hmask⟩ := h
  have h1 := codeMat_xorSelected_mem_spanCodes basis mask
  rw [hmask, codeMat_and_511] at h1
  exact h1

end QiushiMatmul
