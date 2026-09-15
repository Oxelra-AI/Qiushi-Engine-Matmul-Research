import QiushiExtractionBridge
import QiushiCodeSpanCore
import QiushiBranch416Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem branch416_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def branch416MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem branch416_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (branch416MatrixCodeNat M) = M := by decide

lemma branch416_codeMat_matrixCode (M : Mat3) :
    codeMat (branch416MatrixCodeNat M) = M :=
  branch416_codeMat_matrixCode_all M

def redCode416 (M : Mat3) : Nat :=
  redCodeRREF [(272, 8), (4, 2), (1, 0)] (branch416MatrixCodeNat M)

def labelNat416 (M : Mat3) : Nat :=
  (((redCode416 M >>> 1) &&& 1)) +
  2 * (((redCode416 M >>> 3) &&& 1)) +
  4 * (((redCode416 M >>> 4) &&& 1)) +
  8 * (((redCode416 M >>> 5) &&& 1)) +
  16 * (((redCode416 M >>> 6) &&& 1)) +
  32 * (((redCode416 M >>> 7) &&& 1))

private theorem labelNat416_lt_all : ∀ M : Mat3, labelNat416 M < 64 := by decide

def label416 (M : Mat3) : Fin 64 := ⟨labelNat416 M, labelNat416_lt_all M⟩

def sectionCode416 : Fin 64 → Nat := fun q =>
  match q.val with
  | 0 => 0
  | 1 => 2
  | 2 => 8
  | 3 => 10
  | 4 => 16
  | 5 => 18
  | 6 => 24
  | 7 => 26
  | 8 => 32
  | 9 => 34
  | 10 => 40
  | 11 => 42
  | 12 => 48
  | 13 => 50
  | 14 => 56
  | 15 => 58
  | 16 => 64
  | 17 => 66
  | 18 => 72
  | 19 => 74
  | 20 => 80
  | 21 => 82
  | 22 => 88
  | 23 => 90
  | 24 => 96
  | 25 => 98
  | 26 => 104
  | 27 => 106
  | 28 => 112
  | 29 => 114
  | 30 => 120
  | 31 => 122
  | 32 => 128
  | 33 => 130
  | 34 => 136
  | 35 => 138
  | 36 => 144
  | 37 => 146
  | 38 => 152
  | 39 => 154
  | 40 => 160
  | 41 => 162
  | 42 => 168
  | 43 => 170
  | 44 => 176
  | 45 => 178
  | 46 => 184
  | 47 => 186
  | 48 => 192
  | 49 => 194
  | 50 => 200
  | 51 => 202
  | 52 => 208
  | 53 => 210
  | 54 => 216
  | 55 => 218
  | 56 => 224
  | 57 => 226
  | 58 => 232
  | 59 => 234
  | 60 => 240
  | 61 => 242
  | 62 => 248
  | 63 => 250
  | _ => 0

theorem sectionCode416_zero : sectionCode416 ⟨0, by decide⟩ = 0 := rfl

private theorem reconstruction416_bool_all : ∀ M : Mat3,
    spanContainsCodeCore [272, 4, 1]
      (branch416MatrixCodeNat (M + codeMat (sectionCode416 (label416 M)))) = true := by
  decide

theorem reconstruction416_mem (M : Mat3) :
    M + codeMat (sectionCode416 (label416 M)) ∈ o416W := by
  unfold o416W
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 4, 1]
    (branch416MatrixCodeNat (M + codeMat (sectionCode416 (label416 M))))
    (reconstruction416_bool_all M)
  rwa [branch416_codeMat_matrixCode] at hspan

theorem label416_eq_zero_mem (M : Mat3) (h : label416 M = ⟨0, by decide⟩) : M ∈ o416W := by
  have hrec := reconstruction416_mem M
  rw [h, sectionCode416_zero] at hrec
  have h0 : codeMat 0 = (0 : Mat3) := by
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  rwa [h0, add_zero] at hrec

end QiushiMatmul
