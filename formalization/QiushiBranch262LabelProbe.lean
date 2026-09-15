import QiushiExtractionBridge
import QiushiCodeSpanCore
import QiushiBranch262Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem branch262_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def branch262MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem branch262_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (branch262MatrixCodeNat M) = M := by decide

lemma branch262_codeMat_matrixCode (M : Mat3) :
    codeMat (branch262MatrixCodeNat M) = M :=
  branch262_codeMat_matrixCode_all M

def redCode262 (M : Mat3) : Nat :=
  redCodeRREF [(132, 7), (12, 3), (2, 1), (1, 0)] (branch262MatrixCodeNat M)

def labelNat262 (M : Mat3) : Nat :=
  (((redCode262 M >>> 2) &&& 1)) +
  2 * (((redCode262 M >>> 4) &&& 1)) +
  4 * (((redCode262 M >>> 5) &&& 1)) +
  8 * (((redCode262 M >>> 6) &&& 1)) +
  16 * (((redCode262 M >>> 8) &&& 1))

private theorem labelNat262_lt_all : ∀ M : Mat3, labelNat262 M < 32 := by decide

def label262 (M : Mat3) : Fin 32 := ⟨labelNat262 M, labelNat262_lt_all M⟩

def sectionCode262 : Fin 32 → Nat := fun q =>
  match q.val with
  | 0 => 0
  | 1 => 4
  | 2 => 16
  | 3 => 20
  | 4 => 32
  | 5 => 36
  | 6 => 48
  | 7 => 52
  | 8 => 64
  | 9 => 68
  | 10 => 80
  | 11 => 84
  | 12 => 96
  | 13 => 100
  | 14 => 112
  | 15 => 116
  | 16 => 256
  | 17 => 260
  | 18 => 272
  | 19 => 276
  | 20 => 288
  | 21 => 292
  | 22 => 304
  | 23 => 308
  | 24 => 320
  | 25 => 324
  | 26 => 336
  | 27 => 340
  | 28 => 352
  | 29 => 356
  | 30 => 368
  | 31 => 372
  | _ => 0

theorem sectionCode262_zero : sectionCode262 ⟨0, by decide⟩ = 0 := rfl

private theorem reconstruction262_bool_all : ∀ M : Mat3,
    spanContainsCodeCore [132, 12, 2, 1]
      (branch262MatrixCodeNat (M + codeMat (sectionCode262 (label262 M)))) = true := by
  decide

theorem reconstruction262_mem (M : Mat3) :
    M + codeMat (sectionCode262 (label262 M)) ∈ o262W := by
  unfold o262W
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1]
    (branch262MatrixCodeNat (M + codeMat (sectionCode262 (label262 M))))
    (reconstruction262_bool_all M)
  rwa [branch262_codeMat_matrixCode] at hspan

theorem label262_eq_zero_mem (M : Mat3) (h : label262 M = ⟨0, by decide⟩) : M ∈ o262W := by
  have hrec := reconstruction262_mem M
  rw [h, sectionCode262_zero] at hrec
  have h0 : codeMat 0 = (0 : Mat3) := by
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  rwa [h0, add_zero] at hrec

end QiushiMatmul
