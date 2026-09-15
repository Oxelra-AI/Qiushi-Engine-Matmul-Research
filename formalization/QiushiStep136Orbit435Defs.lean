import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiFlattenSeeds

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

def o435W : Submodule F2 Mat3 := spanCodes [193, 19, 10]

def o435AnnBasis : Fin 6 → Mat3
  | ⟨0, _⟩ => codeMat 145
  | ⟨1, _⟩ => codeMat 26
  | ⟨2, _⟩ => codeMat 4
  | ⟨3, _⟩ => codeMat 32
  | ⟨4, _⟩ => codeMat 192
  | ⟨5, _⟩ => codeMat 256
  | ⟨n + 6, h⟩ => absurd h (by omega)

def o435BridgeMatCode (M : Mat3) : Nat :=
  (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
  (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
  (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
  (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
  (if M 2 2 = 1 then 256 else 0)

private theorem o435_codeMat_bridgeCode_all : ∀ M : Mat3, codeMat (o435BridgeMatCode M) = M := by decide
theorem o435_codeMat_bridgeCode (M : Mat3) : codeMat (o435BridgeMatCode M) = M := o435_codeMat_bridgeCode_all M

def o435SourceU : Fin 63 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 401)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 480)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 228) ⊓ kerEvalFunc (codeMat 288)
  | ⟨3, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 222) ⊓ kerEvalFunc (codeMat 282)
  | ⟨4, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 218)
  | ⟨5, _⟩ => kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 401)
  | ⟨6, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 433)
  | ⟨7, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 224) ⊓ kerEvalFunc (codeMat 433)
  | ⟨8, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 405)
  | ⟨9, _⟩ => kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 282)
  | ⟨10, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 433)
  | ⟨11, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 405)
  | ⟨12, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 288)
  | ⟨13, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 433)
  | ⟨14, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 256)
  | ⟨15, _⟩ => kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 256)
  | ⟨16, _⟩ => kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 218) ⊓ kerEvalFunc (codeMat 256)
  | ⟨17, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)
  | ⟨18, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)
  | ⟨19, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)
  | ⟨20, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)
  | ⟨21, _⟩ => kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)
  | ⟨22, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)
  | ⟨23, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)
  | ⟨24, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 405)
  | ⟨25, _⟩ => kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 395)
  | ⟨26, _⟩ => kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 85) ⊓ kerEvalFunc (codeMat 401)
  | ⟨27, _⟩ => kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 405)
  | ⟨28, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 478)
  | ⟨29, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 250) ⊓ kerEvalFunc (codeMat 286)
  | ⟨30, _⟩ => kerEvalFunc (codeMat 30) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 218)
  | ⟨31, _⟩ => kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 113) ⊓ kerEvalFunc (codeMat 427)
  | ⟨32, _⟩ => kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 331)
  | ⟨33, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 452)
  | ⟨34, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 228) ⊓ kerEvalFunc (codeMat 433)
  | ⟨35, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 113) ⊓ kerEvalFunc (codeMat 401)
  | ⟨36, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 337)
  | ⟨37, _⟩ => kerEvalFunc (codeMat 30) ⊓ kerEvalFunc (codeMat 224) ⊓ kerEvalFunc (codeMat 401)
  | ⟨38, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 85)
  | ⟨39, _⟩ => kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 405)
  | ⟨40, _⟩ => kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 286)
  | ⟨41, _⟩ => kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 85) ⊓ kerEvalFunc (codeMat 260)
  | ⟨42, _⟩ => kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 395)
  | ⟨43, _⟩ => kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 282)
  | ⟨44, _⟩ => kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 401)
  | ⟨45, _⟩ => kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 282)
  | ⟨46, _⟩ => kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 395)
  | ⟨47, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 254) ⊓ kerEvalFunc (codeMat 318)
  | ⟨48, _⟩ => kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 222) ⊓ kerEvalFunc (codeMat 286)
  | ⟨49, _⟩ => kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 218) ⊓ kerEvalFunc (codeMat 282)
  | ⟨50, _⟩ => kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 282)
  | ⟨51, _⟩ => kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 250) ⊓ kerEvalFunc (codeMat 314)
  | ⟨52, _⟩ => kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 395)
  | ⟨53, _⟩ => kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 85) ⊓ kerEvalFunc (codeMat 405)
  | ⟨54, _⟩ => kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 337)
  | ⟨55, _⟩ => kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 484)
  | ⟨56, _⟩ => kerEvalFunc (codeMat 228) ⊓ kerEvalFunc (codeMat 433)
  | ⟨57, _⟩ => kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 113)
  | ⟨58, _⟩ => kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 196)
  | ⟨59, _⟩ => kerEvalFunc (codeMat 30) ⊓ kerEvalFunc (codeMat 218)
  | ⟨60, _⟩ => kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 452)
  | ⟨61, _⟩ => kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 480)
  | ⟨62, _⟩ => kerEvalFunc (codeMat 175) ⊓ kerEvalFunc (codeMat 79)
  | ⟨n + 63, h⟩ => absurd h (by omega)

def o435ActualSourceSpan : Fin 63 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [327, 193, 19, 10]
  | ⟨1, _⟩ => spanCodes [288, 161, 96, 19, 10]
  | ⟨2, _⟩ => spanCodes [292, 133, 68, 19, 10]
  | ⟨3, _⟩ => spanCodes [262, 165, 100, 19, 10]
  | ⟨4, _⟩ => spanCodes [256, 163, 98, 19, 10]
  | ⟨5, _⟩ => spanCodes [291, 167, 102, 19, 10]
  | ⟨6, _⟩ => spanCodes [288, 160, 97, 19, 10]
  | ⟨7, _⟩ => spanCodes [257, 160, 97, 19, 10]
  | ⟨8, _⟩ => spanCodes [289, 132, 69, 19, 10]
  | ⟨9, _⟩ => spanCodes [295, 132, 69, 19, 10]
  | ⟨10, _⟩ => spanCodes [288, 164, 101, 19, 10]
  | ⟨11, _⟩ => spanCodes [260, 164, 101, 19, 10]
  | ⟨12, _⟩ => spanCodes [288, 134, 71, 19, 10]
  | ⟨13, _⟩ => spanCodes [288, 166, 103, 19, 10]
  | ⟨14, _⟩ => spanCodes [129, 64, 17, 8, 2]
  | ⟨15, _⟩ => spanCodes [128, 65, 16, 9, 3]
  | ⟨16, _⟩ => spanCodes [130, 66, 18, 10, 1]
  | ⟨17, _⟩ => spanCodes [193, 34, 19, 10, 4]
  | ⟨18, _⟩ => spanCodes [193, 33, 19, 10, 4]
  | ⟨19, _⟩ => spanCodes [193, 34, 19, 10, 6]
  | ⟨20, _⟩ => spanCodes [193, 33, 19, 10, 5]
  | ⟨21, _⟩ => spanCodes [193, 35, 19, 10, 5]
  | ⟨22, _⟩ => spanCodes [193, 32, 19, 10, 7]
  | ⟨23, _⟩ => spanCodes [193, 35, 19, 10, 7]
  | ⟨24, _⟩ => spanCodes [257, 132, 69, 32, 19, 10]
  | ⟨25, _⟩ => spanCodes [262, 134, 71, 36, 19, 10]
  | ⟨26, _⟩ => spanCodes [261, 133, 68, 34, 19, 10]
  | ⟨27, _⟩ => spanCodes [260, 132, 69, 34, 19, 10]
  | ⟨28, _⟩ => spanCodes [260, 133, 68, 38, 19, 10]
  | ⟨29, _⟩ => spanCodes [260, 135, 70, 38, 19, 10]
  | ⟨30, _⟩ => spanCodes [256, 135, 70, 33, 19, 10]
  | ⟨31, _⟩ => spanCodes [258, 134, 71, 37, 19, 10]
  | ⟨32, _⟩ => spanCodes [262, 135, 70, 35, 19, 10]
  | ⟨33, _⟩ => spanCodes [263, 134, 71, 35, 19, 10]
  | ⟨34, _⟩ => spanCodes [259, 133, 68, 39, 19, 10]
  | ⟨35, _⟩ => spanCodes [291, 161, 96, 19, 10, 4]
  | ⟨36, _⟩ => spanCodes [291, 162, 99, 19, 10, 4]
  | ⟨37, _⟩ => spanCodes [257, 161, 96, 19, 10, 6]
  | ⟨38, _⟩ => spanCodes [256, 160, 97, 19, 10, 5]
  | ⟨39, _⟩ => spanCodes [291, 163, 98, 19, 10, 7]
  | ⟨40, _⟩ => spanCodes [291, 160, 97, 19, 10, 7]
  | ⟨41, _⟩ => spanCodes [261, 128, 65, 17, 8, 2]
  | ⟨42, _⟩ => spanCodes [293, 129, 64, 16, 9, 3]
  | ⟨43, _⟩ => spanCodes [258, 128, 64, 18, 10, 1]
  | ⟨44, _⟩ => spanCodes [259, 193, 34, 19, 10, 4]
  | ⟨45, _⟩ => spanCodes [259, 193, 33, 19, 10, 4]
  | ⟨46, _⟩ => spanCodes [322, 193, 35, 19, 10, 4]
  | ⟨47, _⟩ => spanCodes [322, 193, 34, 19, 10, 6]
  | ⟨48, _⟩ => spanCodes [322, 193, 33, 19, 10, 6]
  | ⟨49, _⟩ => spanCodes [323, 193, 32, 19, 10, 5]
  | ⟨50, _⟩ => spanCodes [258, 193, 33, 19, 10, 5]
  | ⟨51, _⟩ => spanCodes [323, 193, 35, 19, 10, 5]
  | ⟨52, _⟩ => spanCodes [258, 193, 32, 19, 10, 7]
  | ⟨53, _⟩ => spanCodes [323, 193, 34, 19, 10, 7]
  | ⟨54, _⟩ => spanCodes [259, 130, 67, 32, 19, 10, 6]
  | ⟨55, _⟩ => spanCodes [260, 133, 68, 36, 17, 8, 2]
  | ⟨56, _⟩ => spanCodes [257, 133, 68, 37, 17, 8, 2]
  | ⟨57, _⟩ => spanCodes [256, 132, 69, 37, 17, 8, 2]
  | ⟨58, _⟩ => spanCodes [256, 132, 68, 32, 18, 10, 1]
  | ⟨59, _⟩ => spanCodes [256, 134, 70, 32, 18, 10, 1]
  | ⟨60, _⟩ => spanCodes [260, 132, 68, 34, 18, 10, 1]
  | ⟨61, _⟩ => spanCodes [288, 161, 96, 16, 9, 4, 3]
  | ⟨62, _⟩ => spanCodes [256, 160, 97, 16, 9, 5, 3]
  | ⟨n + 63, h⟩ => absurd h (by omega)

def o435SourceLb : Fin 63 → ℕ
  | ⟨n, _⟩ => [16, 15, 16, 15, 15, 16, 15, 16, 16, 15, 15, 16, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 12, 12, 12, 12, 12, 12, 12, 12].getD n 0

def o435Lambda : Fin 63 → ℕ
  | ⟨n, _⟩ => [496480, 439598, 187504, 2074020, 3736888, 589190, 2857298, 1071736, 5303770, 330292, 62370, 5130200, 2283954, 249740, 4052760, 4176880, 3928640, 1487616, 2923020, 3699210, 612748, 4902790, 2447082, 138574, 646863, 3935435, 1776032, 2239911, 1876719, 1321668, 2386441, 2734597, 3485615, 1251058, 1917501, 2681793, 1197574, 4258483, 201863, 564086, 3378601, 3928640, 4052760, 4052760, 429844, 861153, 507586, 1538947, 554454, 2065692, 1429102, 1087139, 3359041, 201202, 248240, 804264, 2789836, 582780, 2020906, 1370456, 785518, 2069694, 1858946].getD n 0

def o435ScalarCoverB : Fin 63 → F2 → F2 → F2 → F2 → F2 → F2 → Bool
  | ⟨0, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) = 0 ∧ (x0 + x2) = 0) ∧ x3 = 0) ∧ (x0 + x4) = 0) ∧ (x0 + x5) = 0))
  | ⟨1, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 = 0 ∧ x1 = 0) ∧ x2 = 0) ∧ ((x3 + x4) + x5) = 0))
  | ⟨2, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 = 0 ∧ x1 = 0) ∧ ((x2 + x3) + x4) = 0) ∧ (x3 + x5) = 0))
  | ⟨3, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 = 0 ∧ ((x1 + x2) + x3) = 0) ∧ ((x1 + x2) + x4) = 0) ∧ (x1 + x5) = 0))
  | ⟨4, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 = 0 ∧ x2 = 0) ∧ (x1 + x3) = 0) ∧ (x1 + x4) = 0))
  | ⟨5, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) + x2) = 0 ∧ (x1 + x3) = 0) ∧ ((x0 + x1) + x4) = 0) ∧ (x0 + x5) = 0))
  | ⟨6, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 = 0 ∧ x2 = 0) ∧ (x0 + x4) = 0) ∧ ((x0 + x3) + x5) = 0))
  | ⟨7, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 = 0 ∧ x2 = 0) ∧ (x3 + x4) = 0) ∧ ((x0 + x3) + x5) = 0))
  | ⟨8, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 = 0 ∧ ((x0 + x2) + x3) = 0) ∧ (x2 + x4) = 0) ∧ ((x0 + x2) + x5) = 0))
  | ⟨9, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x2) = 0 ∧ (x1 + x3) = 0) ∧ ((x0 + x1) + x4) = 0) ∧ (x1 + x5) = 0))
  | ⟨10, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 = 0 ∧ (x0 + x2) = 0) ∧ (x0 + x4) = 0) ∧ ((x0 + x3) + x5) = 0))
  | ⟨11, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 = 0 ∧ (x0 + x3) = 0) ∧ (x0 + x4) = 0) ∧ ((x0 + x2) + x5) = 0))
  | ⟨12, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) = 0 ∧ (x0 + x2) = 0) ∧ (x0 + x4) = 0) ∧ (x3 + x5) = 0))
  | ⟨13, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) = 0 ∧ (x0 + x2) = 0) ∧ (x0 + x4) = 0) ∧ ((x0 + x3) + x5) = 0))
  | ⟨14, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 = 0 ∧ x2 = 0) ∧ x3 = 0) ∧ x5 = 0))
  | ⟨15, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x2 = 0 ∧ x3 = 0) ∧ ((x0 + x1) + x4) = 0) ∧ x5 = 0))
  | ⟨16, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x2 = 0 ∧ x3 = 0) ∧ (x1 + x4) = 0) ∧ x5 = 0))
  | ⟨17, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 = 0 ∧ (x1 + x3) = 0) ∧ x4 = 0) ∧ x5 = 0))
  | ⟨18, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 = 0 ∧ (x0 + x3) = 0) ∧ x4 = 0) ∧ x5 = 0))
  | ⟨19, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 = 0 ∧ ((x1 + x2) + x3) = 0) ∧ x4 = 0) ∧ x5 = 0))
  | ⟨20, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 = 0 ∧ ((x0 + x2) + x3) = 0) ∧ x4 = 0) ∧ x5 = 0))
  | ⟨21, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((((x0 + x1) + x2) = 0 ∧ (x1 + x3) = 0) ∧ x4 = 0) ∧ x5 = 0))
  | ⟨22, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) = 0 ∧ (x0 + x2) = 0) ∧ x4 = 0) ∧ x5 = 0))
  | ⟨23, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) = 0 ∧ ((x0 + x2) + x3) = 0) ∧ x4 = 0) ∧ x5 = 0))
  | ⟨24, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x1 = 0 ∧ (x2 + x4) = 0) ∧ ((x0 + x2) + x5) = 0))
  | ⟨25, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x1 + x2) + x3) = 0 ∧ (x0 + x4) = 0) ∧ ((x0 + x1) + x5) = 0))
  | ⟨26, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 + x3) = 0 ∧ ((x0 + x2) + x4) = 0) ∧ (x0 + x5) = 0))
  | ⟨27, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 + x3) = 0 ∧ (x0 + x4) = 0) ∧ ((x0 + x2) + x5) = 0))
  | ⟨28, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 = 0 ∧ (x1 + x3) = 0) ∧ (((x1 + x2) + x4) + x5) = 0))
  | ⟨29, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 = 0 ∧ ((x1 + x3) + x4) = 0) ∧ ((x1 + x2) + x5) = 0))
  | ⟨30, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 + x2) = 0 ∧ (x0 + x3) = 0) ∧ (x1 + x4) = 0))
  | ⟨31, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x2) = 0 ∧ ((x0 + x3) + x4) = 0) ∧ (((x0 + x1) + x3) + x5) = 0))
  | ⟨32, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) = 0 ∧ (x0 + x3) = 0) ∧ (((x0 + x1) + x4) + x5) = 0))
  | ⟨33, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) = 0 ∧ ((x0 + x2) + x3) = 0) ∧ ((x2 + x4) + x5) = 0))
  | ⟨34, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) = 0 ∧ ((x2 + x3) + x4) = 0) ∧ ((x0 + x3) + x5) = 0))
  | ⟨35, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) = 0 ∧ ((x0 + x3) + x4) = 0) ∧ (x0 + x5) = 0))
  | ⟨36, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) = 0 ∧ (x0 + x3) = 0) ∧ ((x0 + x4) + x5) = 0))
  | ⟨37, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x1 + x2) = 0 ∧ (x3 + x4) = 0) ∧ (x0 + x5) = 0))
  | ⟨38, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x1 = 0 ∧ ((x0 + x2) + x3) = 0) ∧ ((x0 + x2) + x4) = 0))
  | ⟨39, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x1 + x2) + x3) = 0 ∧ ((x0 + x1) + x4) = 0) ∧ ((x0 + x2) + x5) = 0))
  | ⟨40, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x2) + x3) = 0 ∧ ((x0 + x1) + x4) = 0) ∧ ((x1 + x2) + x5) = 0))
  | ⟨41, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x3 = 0 ∧ ((x0 + x2) + x4) = 0) ∧ (x2 + x5) = 0))
  | ⟨42, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) = 0 ∧ ((x0 + x1) + x3) = 0) ∧ ((x0 + x1) + x5) = 0))
  | ⟨43, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x2 = 0 ∧ x3 = 0) ∧ (x1 + x5) = 0))
  | ⟨44, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x3) = 0 ∧ x4 = 0) ∧ (x0 + x5) = 0))
  | ⟨45, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x3) = 0 ∧ x4 = 0) ∧ (x1 + x5) = 0))
  | ⟨46, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x3) = 0 ∧ ((x0 + x1) + x4) = 0) ∧ ((x0 + x1) + x5) = 0))
  | ⟨47, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 = 0 ∧ (((x1 + x2) + x3) + x4) = 0) ∧ (((x1 + x2) + x3) + x5) = 0))
  | ⟨48, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x3) = 0 ∧ ((x1 + x2) + x4) = 0) ∧ ((x1 + x2) + x5) = 0))
  | ⟨49, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) = 0 ∧ (x1 + x4) = 0) ∧ (x1 + x5) = 0))
  | ⟨50, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x2) + x3) = 0 ∧ x4 = 0) ∧ (x1 + x5) = 0))
  | ⟨51, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) = 0 ∧ ((x1 + x3) + x4) = 0) ∧ ((x1 + x3) + x5) = 0))
  | ⟨52, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x2) = 0 ∧ x4 = 0) ∧ ((x0 + x1) + x5) = 0))
  | ⟨53, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x3) = 0 ∧ ((x0 + x2) + x4) = 0) ∧ ((x0 + x2) + x5) = 0))
  | ⟨54, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x0 + x1) + x2) = 0 ∧ ((x0 + x4) + x5) = 0))
  | ⟨55, _⟩, x0, x1, x2, x3, x4, x5 => decide ((x0 = 0 ∧ (((x2 + x3) + x4) + x5) = 0))
  | ⟨56, _⟩, x0, x1, x2, x3, x4, x5 => decide ((((x2 + x3) + x4) = 0 ∧ ((x0 + x3) + x5) = 0))
  | ⟨57, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 + x2) = 0 ∧ ((x0 + x3) + x4) = 0))
  | ⟨58, _⟩, x0, x1, x2, x3, x4, x5 => decide ((x1 = 0 ∧ (x2 + x4) = 0))
  | ⟨59, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x1 + x2) = 0 ∧ (x1 + x4) = 0))
  | ⟨60, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x1 + x3) = 0 ∧ ((x2 + x4) + x5) = 0))
  | ⟨61, _⟩, x0, x1, x2, x3, x4, x5 => decide (((x0 + x1) = 0 ∧ ((x3 + x4) + x5) = 0))
  | ⟨62, _⟩, x0, x1, x2, x3, x4, x5 => decide (((((x0 + x1) + x2) + x3) = 0 ∧ (((x0 + x1) + x2) + x4) = 0))
  | ⟨n + 63, h⟩, _, _, _, _, _, _ => absurd h (by omega)

def o435Cover (i : Fin 63) (M : Mat3) : Prop :=
  o435ScalarCoverB i
    (evalFunc (o435AnnBasis ⟨0, by decide⟩) M)
    (evalFunc (o435AnnBasis ⟨1, by decide⟩) M)
    (evalFunc (o435AnnBasis ⟨2, by decide⟩) M)
    (evalFunc (o435AnnBasis ⟨3, by decide⟩) M)
    (evalFunc (o435AnnBasis ⟨4, by decide⟩) M)
    (evalFunc (o435AnnBasis ⟨5, by decide⟩) M)
    = true

private lemma mem_kerEvalFunc_iff435 {L M : Mat3} : M ∈ kerEvalFunc L ↔ evalFunc L M = 0 := Iff.rfl

theorem o435_evalFunc_add_left (L N M : Mat3) :
    evalFunc (L + N) M = evalFunc L M + evalFunc N M := by
  unfold evalFunc; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  show (L + N) i j * M i j = L i j * M i j + N i j * M i j
  rw [show (L + N) i j = L i j + N i j from rfl, add_mul]

theorem o435_funcExp_30 : codeMat 30 = ((codeMat 26 : Mat3) + codeMat 4) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_58 : codeMat 58 = ((codeMat 26 : Mat3) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_62 : codeMat 62 = (((codeMat 26 : Mat3) + codeMat 4) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_75 : codeMat 75 = (((codeMat 145 : Mat3) + codeMat 26) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_79 : codeMat 79 = ((((codeMat 145 : Mat3) + codeMat 26) + codeMat 4) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_81 : codeMat 81 = ((codeMat 145 : Mat3) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_85 : codeMat 85 = (((codeMat 145 : Mat3) + codeMat 4) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_113 : codeMat 113 = (((codeMat 145 : Mat3) + codeMat 32) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_139 : codeMat 139 = ((codeMat 145 : Mat3) + codeMat 26) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_143 : codeMat 143 = (((codeMat 145 : Mat3) + codeMat 26) + codeMat 4) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_149 : codeMat 149 = ((codeMat 145 : Mat3) + codeMat 4) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_171 : codeMat 171 = (((codeMat 145 : Mat3) + codeMat 26) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_175 : codeMat 175 = ((((codeMat 145 : Mat3) + codeMat 26) + codeMat 4) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_177 : codeMat 177 = ((codeMat 145 : Mat3) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_181 : codeMat 181 = (((codeMat 145 : Mat3) + codeMat 4) + codeMat 32) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_196 : codeMat 196 = ((codeMat 4 : Mat3) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_218 : codeMat 218 = ((codeMat 26 : Mat3) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_222 : codeMat 222 = (((codeMat 26 : Mat3) + codeMat 4) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_224 : codeMat 224 = ((codeMat 32 : Mat3) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_228 : codeMat 228 = (((codeMat 4 : Mat3) + codeMat 32) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_250 : codeMat 250 = (((codeMat 26 : Mat3) + codeMat 32) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_254 : codeMat 254 = ((((codeMat 26 : Mat3) + codeMat 4) + codeMat 32) + codeMat 192) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_260 : codeMat 260 = ((codeMat 4 : Mat3) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_282 : codeMat 282 = ((codeMat 26 : Mat3) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_286 : codeMat 286 = (((codeMat 26 : Mat3) + codeMat 4) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_288 : codeMat 288 = ((codeMat 32 : Mat3) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_314 : codeMat 314 = (((codeMat 26 : Mat3) + codeMat 32) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_318 : codeMat 318 = ((((codeMat 26 : Mat3) + codeMat 4) + codeMat 32) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_331 : codeMat 331 = ((((codeMat 145 : Mat3) + codeMat 26) + codeMat 192) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_337 : codeMat 337 = (((codeMat 145 : Mat3) + codeMat 192) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_395 : codeMat 395 = (((codeMat 145 : Mat3) + codeMat 26) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_401 : codeMat 401 = ((codeMat 145 : Mat3) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_405 : codeMat 405 = (((codeMat 145 : Mat3) + codeMat 4) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_427 : codeMat 427 = ((((codeMat 145 : Mat3) + codeMat 26) + codeMat 32) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_433 : codeMat 433 = (((codeMat 145 : Mat3) + codeMat 32) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_452 : codeMat 452 = (((codeMat 4 : Mat3) + codeMat 192) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_478 : codeMat 478 = ((((codeMat 26 : Mat3) + codeMat 4) + codeMat 192) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_480 : codeMat 480 = (((codeMat 32 : Mat3) + codeMat 192) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

theorem o435_funcExp_484 : codeMat 484 = ((((codeMat 4 : Mat3) + codeMat 32) + codeMat 192) + codeMat 256) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

end QiushiMatmul
end
