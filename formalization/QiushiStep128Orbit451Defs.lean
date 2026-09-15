import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

def o451W : Submodule F2 Mat3 := spanCodes [257, 19, 10]
def o451AnnBasis : Fin 6 → Mat3
  | ⟨0, _⟩ => codeMat 273
  | ⟨1, _⟩ => codeMat 26
  | ⟨2, _⟩ => codeMat 4
  | ⟨3, _⟩ => codeMat 32
  | ⟨4, _⟩ => codeMat 64
  | ⟨5, _⟩ => codeMat 128
  | ⟨n + 6, h⟩ => absurd h (by omega)

def o451BridgeMatCode (M : Mat3) : Nat :=
  (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
  (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
  (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
  (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
  (if M 2 2 = 1 then 256 else 0)

private theorem o451_codeMat_bridgeCode_all : ∀ M : Mat3, codeMat (o451BridgeMatCode M) = M := by decide
theorem o451_codeMat_bridgeCode (M : Mat3) : codeMat (o451BridgeMatCode M) = M := o451_codeMat_bridgeCode_all M

def o451SourceU : Fin 44 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 273) ⊓ kerEvalFunc (codeMat 154) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 4)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 30)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 30)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 36) ⊓ kerEvalFunc (codeMat 30)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 36) ⊓ kerEvalFunc (codeMat 30)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 90) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 4)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 363) ⊓ kerEvalFunc (codeMat 224) ⊓ kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 395) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 36) ⊓ kerEvalFunc (codeMat 26)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 331) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 26)
  | ⟨9, _⟩ => kerEvalFunc (codeMat 335) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 26)
  | ⟨10, _⟩ => kerEvalFunc (codeMat 299) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 26)
  | ⟨11, _⟩ => kerEvalFunc (codeMat 299) ⊓ kerEvalFunc (codeMat 164) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 26)
  | ⟨12, _⟩ => kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 26)
  | ⟨13, _⟩ => kerEvalFunc (codeMat 303) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 26)
  | ⟨14, _⟩ => kerEvalFunc (codeMat 273) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 4)
  | ⟨15, _⟩ => kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 4)
  | ⟨16, _⟩ => kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 100) ⊓ kerEvalFunc (codeMat 26)
  | ⟨17, _⟩ => kerEvalFunc (codeMat 164) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 26)
  | ⟨18, _⟩ => kerEvalFunc (codeMat 273) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 64)
  | ⟨19, _⟩ => kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 64)
  | ⟨20, _⟩ => kerEvalFunc (codeMat 401) ⊓ kerEvalFunc (codeMat 122)
  | ⟨21, _⟩ => kerEvalFunc (codeMat 369) ⊓ kerEvalFunc (codeMat 250)
  | ⟨22, _⟩ => kerEvalFunc (codeMat 335) ⊓ kerEvalFunc (codeMat 158)
  | ⟨23, _⟩ => kerEvalFunc (codeMat 337) ⊓ kerEvalFunc (codeMat 254)
  | ⟨24, _⟩ => kerEvalFunc (codeMat 305) ⊓ kerEvalFunc (codeMat 158)
  | ⟨25, _⟩ => kerEvalFunc (codeMat 303) ⊓ kerEvalFunc (codeMat 94)
  | ⟨26, _⟩ => kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 250)
  | ⟨27, _⟩ => kerEvalFunc (codeMat 299) ⊓ kerEvalFunc (codeMat 190)
  | ⟨28, _⟩ => kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 26)
  | ⟨29, _⟩ => kerEvalFunc (codeMat 100) ⊓ kerEvalFunc (codeMat 26)
  | ⟨30, _⟩ => kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 26)
  | ⟨31, _⟩ => kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 100)
  | ⟨32, _⟩ => kerEvalFunc (codeMat 369)
  | ⟨33, _⟩ => kerEvalFunc (codeMat 405)
  | ⟨34, _⟩ => kerEvalFunc (codeMat 501)
  | ⟨35, _⟩ => kerEvalFunc (codeMat 491)
  | ⟨36, _⟩ => kerEvalFunc (codeMat 335)
  | ⟨37, _⟩ => kerEvalFunc (codeMat 431)
  | ⟨38, _⟩ => kerEvalFunc (codeMat 122)
  | ⟨39, _⟩ => kerEvalFunc (codeMat 250)
  | ⟨40, _⟩ => kerEvalFunc (codeMat 158)
  | ⟨41, _⟩ => kerEvalFunc (codeMat 94)
  | ⟨42, _⟩ => kerEvalFunc (codeMat 190)
  | ⟨43, _⟩ => kerEvalFunc (codeMat 254)
  | ⟨n + 44, h⟩ => absurd h (by omega)

def o451ActualSourceSpan : Fin 44 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [257, 162, 19, 10]
  | ⟨1, _⟩ => spanCodes [257, 198, 19, 10]
  | ⟨2, _⟩ => spanCodes [257, 135, 19, 10]
  | ⟨3, _⟩ => spanCodes [257, 231, 19, 10]
  | ⟨4, _⟩ => spanCodes [257, 102, 19, 10]
  | ⟨5, _⟩ => spanCodes [257, 99, 19, 10]
  | ⟨6, _⟩ => spanCodes [257, 161, 96, 19, 10]
  | ⟨7, _⟩ => spanCodes [257, 129, 100, 19, 10]
  | ⟨8, _⟩ => spanCodes [257, 132, 65, 19, 10]
  | ⟨9, _⟩ => spanCodes [257, 133, 65, 19, 10]
  | ⟨10, _⟩ => spanCodes [257, 196, 33, 19, 10]
  | ⟨11, _⟩ => spanCodes [257, 132, 37, 19, 10]
  | ⟨12, _⟩ => spanCodes [257, 96, 19, 10, 5]
  | ⟨13, _⟩ => spanCodes [257, 97, 19, 10, 5]
  | ⟨14, _⟩ => spanCodes [257, 128, 64, 17, 8, 2]
  | ⟨15, _⟩ => spanCodes [257, 128, 64, 16, 9, 3]
  | ⟨16, _⟩ => spanCodes [256, 164, 96, 18, 10, 1]
  | ⟨17, _⟩ => spanCodes [256, 132, 100, 18, 10, 1]
  | ⟨18, _⟩ => spanCodes [257, 32, 17, 8, 4, 2]
  | ⟨19, _⟩ => spanCodes [257, 32, 16, 9, 4, 3]
  | ⟨20, _⟩ => spanCodes [257, 129, 66, 34, 19, 10, 4]
  | ⟨21, _⟩ => spanCodes [257, 130, 67, 35, 19, 10, 4]
  | ⟨22, _⟩ => spanCodes [257, 131, 65, 32, 19, 10, 6]
  | ⟨23, _⟩ => spanCodes [257, 130, 67, 34, 19, 10, 6]
  | ⟨24, _⟩ => spanCodes [257, 130, 64, 33, 19, 10, 6]
  | ⟨25, _⟩ => spanCodes [257, 128, 67, 33, 19, 10, 6]
  | ⟨26, _⟩ => spanCodes [257, 131, 67, 35, 19, 10, 5]
  | ⟨27, _⟩ => spanCodes [257, 131, 64, 34, 19, 10, 7]
  | ⟨28, _⟩ => spanCodes [256, 132, 68, 32, 18, 10, 1]
  | ⟨29, _⟩ => spanCodes [256, 128, 68, 36, 18, 10, 1]
  | ⟨30, _⟩ => spanCodes [256, 160, 64, 18, 10, 4, 1]
  | ⟨31, _⟩ => spanCodes [256, 164, 68, 16, 8, 2, 1]
  | ⟨32, _⟩ => spanCodes [257, 128, 65, 33, 17, 8, 4, 2]
  | ⟨33, _⟩ => spanCodes [257, 129, 64, 32, 17, 8, 5, 2]
  | ⟨34, _⟩ => spanCodes [257, 129, 65, 33, 17, 8, 5, 2]
  | ⟨35, _⟩ => spanCodes [257, 129, 65, 33, 16, 9, 4, 3]
  | ⟨36, _⟩ => spanCodes [257, 128, 65, 32, 16, 9, 5, 3]
  | ⟨37, _⟩ => spanCodes [257, 129, 64, 33, 16, 9, 5, 3]
  | ⟨38, _⟩ => spanCodes [256, 128, 66, 34, 18, 10, 4, 1]
  | ⟨39, _⟩ => spanCodes [256, 130, 66, 34, 18, 10, 4, 1]
  | ⟨40, _⟩ => spanCodes [256, 130, 64, 32, 18, 10, 6, 1]
  | ⟨41, _⟩ => spanCodes [256, 128, 66, 32, 18, 10, 6, 1]
  | ⟨42, _⟩ => spanCodes [256, 130, 64, 34, 18, 10, 6, 1]
  | ⟨43, _⟩ => spanCodes [256, 130, 66, 34, 18, 10, 6, 1]
  | ⟨n + 44, h⟩ => absurd h (by omega)

def o451SourceLb : Fin 44 → ℕ
  | ⟨n, _⟩ => [17, 17, 17, 17, 17, 17, 16, 16, 16, 16, 16, 16, 16, 16, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14, 14, 14, 14, 14, 12, 12, 12, 12, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9].getD n 0
def o451Lambda : Fin 44 → ℕ
  | ⟨n, _⟩ => [32, 32, 32, 32, 32, 32, 4, 4, 4, 4, 4, 4, 4, 4, 12, 4, 4, 4, 4, 12, 6, 2, 4, 4, 2, 4, 4, 6, 6, 6, 4, 8, 5, 5, 6, 5, 6, 5, 1, 1, 1, 2, 1, 2].getD n 0

def o451ScalarCoverB : Fin 44 → F2 → F2 → F2 → F2 → F2 → F2 → Bool
  | ⟨0, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 = 0 ∧ (x1 + x5) = 0) ∧ x4 = 0) ∧ (x1 + x3) = 0) ∧ x2 = 0))
  | ⟨1, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((((x0 + x1) + x2) = 0 ∧ (x2 + x5) = 0) ∧ (x2 + x4) = 0) ∧ x3 = 0) ∧ (x1 + x2) = 0))
  | ⟨2, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) = 0 ∧ (x2 + x5) = 0) ∧ x4 = 0) ∧ x3 = 0) ∧ (x1 + x2) = 0))
  | ⟨3, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) = 0 ∧ (x2 + x5) = 0) ∧ (x2 + x4) = 0) ∧ (x2 + x3) = 0) ∧ (x1 + x2) = 0))
  | ⟨4, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((((x0 + x1) + x2) = 0 ∧ x5 = 0) ∧ (x2 + x4) = 0) ∧ (x2 + x3) = 0) ∧ (x1 + x2) = 0))
  | ⟨5, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) = 0 ∧ x5 = 0) ∧ (x1 + x4) = 0) ∧ (x1 + x3) = 0) ∧ x2 = 0))
  | ⟨6, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((((x0 + x1) + x3) + x4) = 0 ∧ ((x3 + x4) + x5) = 0) ∧ x1 = 0) ∧ x2 = 0))
  | ⟨7, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) + x5) = 0 ∧ (x2 + x4) = 0) ∧ (x2 + x3) = 0) ∧ x1 = 0))
  | ⟨8, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) + x4) = 0 ∧ (x2 + x5) = 0) ∧ x3 = 0) ∧ x1 = 0))
  | ⟨9, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((((x0 + x1) + x2) + x4) = 0 ∧ (x2 + x5) = 0) ∧ x3 = 0) ∧ x1 = 0))
  | ⟨10, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) + x3) = 0 ∧ (x2 + x5) = 0) ∧ (x2 + x4) = 0) ∧ x1 = 0))
  | ⟨11, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) + x3) = 0 ∧ ((x2 + x3) + x5) = 0) ∧ x4 = 0) ∧ x1 = 0))
  | ⟨12, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) + x2) = 0 ∧ x5 = 0) ∧ (x3 + x4) = 0) ∧ x1 = 0))
  | ⟨13, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((((x0 + x1) + x2) + x3) = 0 ∧ x5 = 0) ∧ (x3 + x4) = 0) ∧ x1 = 0))
  | ⟨14, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 = 0 ∧ x3 = 0) ∧ x2 = 0))
  | ⟨15, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) = 0 ∧ x3 = 0) ∧ x2 = 0))
  | ⟨16, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x2 + x5) = 0 ∧ ((x2 + x3) + x4) = 0) ∧ x1 = 0))
  | ⟨17, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x2 + x3) + x5) = 0 ∧ (x3 + x4) = 0) ∧ x1 = 0))
  | ⟨18, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 = 0 ∧ x5 = 0) ∧ x4 = 0))
  | ⟨19, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) = 0 ∧ x5 = 0) ∧ x4 = 0))
  | ⟨20, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 + x5) = 0 ∧ ((x1 + x3) + x4) = 0))
  | ⟨21, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x3) + x4) = 0 ∧ (((x1 + x3) + x4) + x5) = 0))
  | ⟨22, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) + x4) = 0 ∧ ((x1 + x2) + x5) = 0))
  | ⟨23, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 + x4) = 0 ∧ ((((x1 + x2) + x3) + x4) + x5) = 0))
  | ⟨24, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 + x3) = 0 ∧ ((x1 + x2) + x5) = 0))
  | ⟨25, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) + x3) = 0 ∧ ((x1 + x2) + x4) = 0))
  | ⟨26, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) + x2) = 0 ∧ (((x1 + x3) + x4) + x5) = 0))
  | ⟨27, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) + x3) = 0 ∧ (((x1 + x2) + x3) + x5) = 0))
  | ⟨28, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x2 + x4) + x5) = 0 ∧ x1 = 0))
  | ⟨29, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x2 + x3) + x4) = 0 ∧ x1 = 0))
  | ⟨30, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x3 + x5) = 0 ∧ x1 = 0))
  | ⟨31, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x3 + x5) = 0 ∧ ((x2 + x3) + x4) = 0))
  | ⟨32, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 + x3) + x4) = 0)
  | ⟨33, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 + x2) + x5) = 0)
  | ⟨34, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x2) + x3) + x4) + x5) = 0)
  | ⟨35, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x3) + x4) + x5) = 0)
  | ⟨36, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) + x2) + x4) = 0)
  | ⟨37, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) + x3) + x5) = 0)
  | ⟨38, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x1 + x3) + x4) = 0)
  | ⟨39, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 + x3) + x4) + x5) = 0)
  | ⟨40, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x1 + x2) + x5) = 0)
  | ⟨41, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x1 + x2) + x4) = 0)
  | ⟨42, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 + x2) + x3) + x5) = 0)
  | ⟨43, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x1 + x2) + x3) + x4) + x5) = 0)
  | ⟨n + 44, h⟩, _, _, _, _, _, _ => absurd h (by omega)

def o451Cover (i : Fin 44) (M : Mat3) : Prop :=
  o451ScalarCoverB i
    (evalFunc (o451AnnBasis ⟨0, by decide⟩) M)
    (evalFunc (o451AnnBasis ⟨1, by decide⟩) M)
    (evalFunc (o451AnnBasis ⟨2, by decide⟩) M)
    (evalFunc (o451AnnBasis ⟨3, by decide⟩) M)
    (evalFunc (o451AnnBasis ⟨4, by decide⟩) M)
    (evalFunc (o451AnnBasis ⟨5, by decide⟩) M)
    = true

private lemma mem_kerEvalFunc_iff451 {L M : Mat3} : M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

private theorem o451_evalFunc_add_left (L N M : Mat3) :
    evalFunc (L + N) M = evalFunc L M + evalFunc N M := by
  unfold evalFunc; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  show (L + N) i j * M i j = L i j * M i j + N i j * M i j
  rw [show (L + N) i j = L i j + N i j from rfl, add_mul]

theorem o451_funcExp_30 : codeMat 30 = ((codeMat 26 : Mat3) + codeMat 4) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_36 : codeMat 36 = ((codeMat 4 : Mat3) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_58 : codeMat 58 = ((codeMat 26 : Mat3) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_68 : codeMat 68 = ((codeMat 4 : Mat3) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_90 : codeMat 90 = ((codeMat 26 : Mat3) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_94 : codeMat 94 = (((codeMat 26 : Mat3) + codeMat 4) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_96 : codeMat 96 = ((codeMat 32 : Mat3) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_100 : codeMat 100 = (((codeMat 4 : Mat3) + codeMat 32) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_122 : codeMat 122 = (((codeMat 26 : Mat3) + codeMat 32) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_132 : codeMat 132 = ((codeMat 4 : Mat3) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_154 : codeMat 154 = ((codeMat 26 : Mat3) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_158 : codeMat 158 = (((codeMat 26 : Mat3) + codeMat 4) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_160 : codeMat 160 = ((codeMat 32 : Mat3) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_164 : codeMat 164 = (((codeMat 4 : Mat3) + codeMat 32) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_190 : codeMat 190 = ((((codeMat 26 : Mat3) + codeMat 4) + codeMat 32) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_196 : codeMat 196 = (((codeMat 4 : Mat3) + codeMat 64) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_224 : codeMat 224 = (((codeMat 32 : Mat3) + codeMat 64) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_250 : codeMat 250 = ((((codeMat 26 : Mat3) + codeMat 32) + codeMat 64) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_254 : codeMat 254 = (((((codeMat 26 : Mat3) + codeMat 4) + codeMat 32) + codeMat 64) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_267 : codeMat 267 = ((codeMat 273 : Mat3) + codeMat 26) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_271 : codeMat 271 = (((codeMat 273 : Mat3) + codeMat 26) + codeMat 4) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_299 : codeMat 299 = (((codeMat 273 : Mat3) + codeMat 26) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_303 : codeMat 303 = ((((codeMat 273 : Mat3) + codeMat 26) + codeMat 4) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_305 : codeMat 305 = ((codeMat 273 : Mat3) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_331 : codeMat 331 = (((codeMat 273 : Mat3) + codeMat 26) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_335 : codeMat 335 = ((((codeMat 273 : Mat3) + codeMat 26) + codeMat 4) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_337 : codeMat 337 = ((codeMat 273 : Mat3) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_363 : codeMat 363 = ((((codeMat 273 : Mat3) + codeMat 26) + codeMat 32) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_369 : codeMat 369 = (((codeMat 273 : Mat3) + codeMat 32) + codeMat 64) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_395 : codeMat 395 = (((codeMat 273 : Mat3) + codeMat 26) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_401 : codeMat 401 = ((codeMat 273 : Mat3) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_405 : codeMat 405 = (((codeMat 273 : Mat3) + codeMat 4) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_431 : codeMat 431 = (((((codeMat 273 : Mat3) + codeMat 26) + codeMat 4) + codeMat 32) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_491 : codeMat 491 = (((((codeMat 273 : Mat3) + codeMat 26) + codeMat 32) + codeMat 64) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o451_funcExp_501 : codeMat 501 = (((((codeMat 273 : Mat3) + codeMat 4) + codeMat 32) + codeMat 64) + codeMat 128) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

end QiushiMatmul
end
