import QiushiExtractionBridge
import QiushiCodeSpanCore
import QiushiStep103Orbit279Dispatches

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section

namespace QiushiMatmul

private theorem step103o279_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step103o279MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step103o279_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step103o279MatrixCodeNat M) = M := by decide

lemma step103o279_codeMat_matrixCode (M : Mat3) :
    codeMat (step103o279MatrixCodeNat M) = M :=
  step103o279_codeMat_matrixCode_all M

def redCode279 (M : Mat3) : Nat :=
  redCodeRREF [(68, 6), (16, 4), (10, 3), (1, 0)] (step103o279MatrixCodeNat M)

def labelNat279 (M : Mat3) : Nat :=
  ((redCode279 M >>> 1) &&& 1) +
  2 * (((redCode279 M >>> 2) &&& 1)) +
  4 * (((redCode279 M >>> 5) &&& 1)) +
  8 * (((redCode279 M >>> 7) &&& 1)) +
  16 * (((redCode279 M >>> 8) &&& 1))

private theorem labelNat279_lt_all : ∀ M : Mat3, labelNat279 M < 32 := by decide

def label279 (M : Mat3) : Fin 32 := ⟨labelNat279 M, labelNat279_lt_all M⟩

def sectionCode279 : Fin 32 → Nat := fun q =>
  match q.val with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 32
  | 5 => 34
  | 6 => 36
  | 7 => 38
  | 8 => 128
  | 9 => 130
  | 10 => 132
  | 11 => 134
  | 12 => 160
  | 13 => 162
  | 14 => 164
  | 15 => 166
  | 16 => 256
  | 17 => 258
  | 18 => 260
  | 19 => 262
  | 20 => 288
  | 21 => 290
  | 22 => 292
  | 23 => 294
  | 24 => 384
  | 25 => 386
  | 26 => 388
  | 27 => 390
  | 28 => 416
  | 29 => 418
  | 30 => 420
  | 31 => 422
  | _ => 0

theorem sectionCode279_zero : sectionCode279 ⟨0, by decide⟩ = 0 := rfl

private theorem reconstruction279_bool_all : ∀ M : Mat3,
    spanContainsCodeCore [68, 16, 10, 1]
      (step103o279MatrixCodeNat (M + codeMat (sectionCode279 (label279 M)))) = true := by
  decide

theorem reconstruction279_mem (M : Mat3) :
    M + codeMat (sectionCode279 (label279 M)) ∈ o279W := by
  unfold o279W
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1]
    (step103o279MatrixCodeNat (M + codeMat (sectionCode279 (label279 M))))
    (reconstruction279_bool_all M)
  rwa [step103o279_codeMat_matrixCode] at hspan

theorem label279_eq_zero_mem (M : Mat3) (h : label279 M = ⟨0, by decide⟩) : M ∈ o279W := by
  have hrec := reconstruction279_mem M
  rw [h, sectionCode279_zero] at hrec
  have h0 : codeMat 0 = (0 : Mat3) := by
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  rwa [h0, add_zero] at hrec

end QiushiMatmul
