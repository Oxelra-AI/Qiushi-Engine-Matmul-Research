import QiushiExtractionBridge
import QiushiCodeSpanCore
import QiushiStep107Orbit373Dispatches

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step107o373_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step107o373MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step107o373_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step107o373MatrixCodeNat M) = M := by decide

lemma step107o373_codeMat_matrixCode (M : Mat3) :
    codeMat (step107o373MatrixCodeNat M) = M :=
  step107o373_codeMat_matrixCode_all M

def redCode373 (M : Mat3) : Nat :=
  redCodeRREF [(1, 0), (20, 4), (224, 7), (300, 8)] (step107o373MatrixCodeNat M)

def labelNat373 (M : Mat3) : Nat :=
  (((redCode373 M >>> 1) &&& 1)) +
  2 * (((redCode373 M >>> 2) &&& 1)) +
  4 * (((redCode373 M >>> 3) &&& 1)) +
  8 * (((redCode373 M >>> 5) &&& 1)) +
  16 * (((redCode373 M >>> 6) &&& 1))

private theorem labelNat373_lt_all : ∀ M : Mat3, labelNat373 M < 32 := by decide

def label373 (M : Mat3) : Fin 32 := ⟨labelNat373 M, labelNat373_lt_all M⟩

def sectionCode373 : Fin 32 → Nat := fun q =>
  match q.val with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 10
  | 6 => 12
  | 7 => 14
  | 8 => 32
  | 9 => 34
  | 10 => 36
  | 11 => 38
  | 12 => 40
  | 13 => 42
  | 14 => 44
  | 15 => 46
  | 16 => 64
  | 17 => 66
  | 18 => 68
  | 19 => 70
  | 20 => 72
  | 21 => 74
  | 22 => 76
  | 23 => 78
  | 24 => 96
  | 25 => 98
  | 26 => 100
  | 27 => 102
  | 28 => 104
  | 29 => 106
  | 30 => 108
  | 31 => 110
  | _ => 0

theorem sectionCode373_zero : sectionCode373 ⟨0, by decide⟩ = 0 := rfl

private theorem reconstruction373_bool_all : ∀ M : Mat3,
    spanContainsCodeCore [300, 224, 20, 1]
      (step107o373MatrixCodeNat (M + codeMat (sectionCode373 (label373 M)))) = true := by
  decide

theorem reconstruction373_mem (M : Mat3) :
    M + codeMat (sectionCode373 (label373 M)) ∈ o373W := by
  unfold o373W
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [300, 224, 20, 1]
    (step107o373MatrixCodeNat (M + codeMat (sectionCode373 (label373 M))))
    (reconstruction373_bool_all M)
  rwa [step107o373_codeMat_matrixCode] at hspan

theorem label373_eq_zero_mem (M : Mat3) (h : label373 M = ⟨0, by decide⟩) : M ∈ o373W := by
  have hrec := reconstruction373_mem M
  rw [h, sectionCode373_zero] at hrec
  have h0 : codeMat 0 = (0 : Mat3) := by
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  rwa [h0, add_zero] at hrec

end QiushiMatmul
