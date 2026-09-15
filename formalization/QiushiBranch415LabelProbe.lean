import QiushiExtractionBridge
import QiushiCodeSpanCore
import QiushiBranch415Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem branch415_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def branch415MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) +
    (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) +
    (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) +
    (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) +
    (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem branch415_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (branch415MatrixCodeNat M) = M := by decide

lemma branch415_codeMat_matrixCode (M : Mat3) :
    codeMat (branch415MatrixCodeNat M) = M :=
  branch415_codeMat_matrixCode_all M

def redCode415 (M : Mat3) : Nat :=
  redCodeRREF [(273, 8), (4, 2), (2, 1)] (branch415MatrixCodeNat M)

def labelNat415 (M : Mat3) : Nat :=
  (((redCode415 M >>> 0) &&& 1)) +
  2 * (((redCode415 M >>> 3) &&& 1)) +
  4 * (((redCode415 M >>> 4) &&& 1)) +
  8 * (((redCode415 M >>> 5) &&& 1)) +
  16 * (((redCode415 M >>> 6) &&& 1)) +
  32 * (((redCode415 M >>> 7) &&& 1))

private theorem labelNat415_lt_all : ∀ M : Mat3, labelNat415 M < 64 := by decide

def label415 (M : Mat3) : Fin 64 := ⟨labelNat415 M, labelNat415_lt_all M⟩

def sectionCode415 : Fin 64 → Nat := fun q =>
  match q.val with
  | 0 => 0
  | 1 => 1
  | 2 => 8
  | 3 => 9
  | 4 => 16
  | 5 => 17
  | 6 => 24
  | 7 => 25
  | 8 => 32
  | 9 => 33
  | 10 => 40
  | 11 => 41
  | 12 => 48
  | 13 => 49
  | 14 => 56
  | 15 => 57
  | 16 => 64
  | 17 => 65
  | 18 => 72
  | 19 => 73
  | 20 => 80
  | 21 => 81
  | 22 => 88
  | 23 => 89
  | 24 => 96
  | 25 => 97
  | 26 => 104
  | 27 => 105
  | 28 => 112
  | 29 => 113
  | 30 => 120
  | 31 => 121
  | 32 => 128
  | 33 => 129
  | 34 => 136
  | 35 => 137
  | 36 => 144
  | 37 => 145
  | 38 => 152
  | 39 => 153
  | 40 => 160
  | 41 => 161
  | 42 => 168
  | 43 => 169
  | 44 => 176
  | 45 => 177
  | 46 => 184
  | 47 => 185
  | 48 => 192
  | 49 => 193
  | 50 => 200
  | 51 => 201
  | 52 => 208
  | 53 => 209
  | 54 => 216
  | 55 => 217
  | 56 => 224
  | 57 => 225
  | 58 => 232
  | 59 => 233
  | 60 => 240
  | 61 => 241
  | 62 => 248
  | 63 => 249
  | _ => 0

theorem sectionCode415_zero : sectionCode415 ⟨0, by decide⟩ = 0 := rfl

private theorem reconstruction415_bool_all : ∀ M : Mat3,
    spanContainsCodeCore [273, 4, 2]
      (branch415MatrixCodeNat (M + codeMat (sectionCode415 (label415 M)))) = true := by
  decide

theorem reconstruction415_mem (M : Mat3) :
    M + codeMat (sectionCode415 (label415 M)) ∈ o415W := by
  unfold o415W
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [273, 4, 2]
    (branch415MatrixCodeNat (M + codeMat (sectionCode415 (label415 M))))
    (reconstruction415_bool_all M)
  rwa [branch415_codeMat_matrixCode] at hspan

theorem label415_eq_zero_mem (M : Mat3) (h : label415 M = ⟨0, by decide⟩) : M ∈ o415W := by
  have hrec := reconstruction415_mem M
  rw [h, sectionCode415_zero] at hrec
  have h0 : codeMat 0 = (0 : Mat3) := by
    ext i j <;> fin_cases i <;> fin_cases j <;> decide
  rwa [h0, add_zero] at hrec

end QiushiMatmul
