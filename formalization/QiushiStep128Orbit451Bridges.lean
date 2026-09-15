import QiushiStep128Orbit451Defs

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o451s0_sourceU_le_actual :
    o451SourceU ⟨0, by omega⟩ ≤ o451ActualSourceSpan ⟨0, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 162, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 273) ⊓ kerEvalFunc (codeMat 154) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 4)) at hM
    change ((((evalFunc (codeMat 273) M = 0 ∧ evalFunc (codeMat 154) M = 0) ∧ evalFunc (codeMat 64) M = 0) ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 4) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 162, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s1_sourceU_le_actual :
    o451SourceU ⟨1, by omega⟩ ≤ o451ActualSourceSpan ⟨1, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 198, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 30)) at hM
    change ((((evalFunc (codeMat 271) M = 0 ∧ evalFunc (codeMat 132) M = 0) ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 30) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 198, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s2_sourceU_le_actual :
    o451SourceU ⟨2, by omega⟩ ≤ o451ActualSourceSpan ⟨2, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 135, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 30)) at hM
    change ((((evalFunc (codeMat 267) M = 0 ∧ evalFunc (codeMat 132) M = 0) ∧ evalFunc (codeMat 64) M = 0) ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 30) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 135, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s3_sourceU_le_actual :
    o451SourceU ⟨3, by omega⟩ ≤ o451ActualSourceSpan ⟨3, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 231, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 36) ⊓ kerEvalFunc (codeMat 30)) at hM
    change ((((evalFunc (codeMat 267) M = 0 ∧ evalFunc (codeMat 132) M = 0) ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 36) M = 0) ∧ evalFunc (codeMat 30) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 231, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s4_sourceU_le_actual :
    o451SourceU ⟨4, by omega⟩ ≤ o451ActualSourceSpan ⟨4, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 102, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 36) ⊓ kerEvalFunc (codeMat 30)) at hM
    change ((((evalFunc (codeMat 271) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 36) M = 0) ∧ evalFunc (codeMat 30) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 102, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s5_sourceU_le_actual :
    o451SourceU ⟨5, by omega⟩ ≤ o451ActualSourceSpan ⟨5, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 99, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 90) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 4)) at hM
    change ((((evalFunc (codeMat 267) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 90) M = 0) ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 4) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 99, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s6_sourceU_le_actual :
    o451SourceU ⟨6, by omega⟩ ≤ o451ActualSourceSpan ⟨6, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 161, 96, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 363) ⊓ kerEvalFunc (codeMat 224) ⊓ kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4)) at hM
    change (((evalFunc (codeMat 363) M = 0 ∧ evalFunc (codeMat 224) M = 0) ∧ evalFunc (codeMat 26) M = 0) ∧ evalFunc (codeMat 4) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 161, 96, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s7_sourceU_le_actual :
    o451SourceU ⟨7, by omega⟩ ≤ o451ActualSourceSpan ⟨7, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 129, 100, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 395) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 36) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 395) M = 0 ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 36) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 129, 100, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s8_sourceU_le_actual :
    o451SourceU ⟨8, by omega⟩ ≤ o451ActualSourceSpan ⟨8, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 132, 65, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 331) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 331) M = 0 ∧ evalFunc (codeMat 132) M = 0) ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 132, 65, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s9_sourceU_le_actual :
    o451SourceU ⟨9, by omega⟩ ≤ o451ActualSourceSpan ⟨9, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 133, 65, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 335) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 335) M = 0 ∧ evalFunc (codeMat 132) M = 0) ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 133, 65, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s10_sourceU_le_actual :
    o451SourceU ⟨10, by omega⟩ ≤ o451ActualSourceSpan ⟨10, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 196, 33, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 299) ⊓ kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 68) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 299) M = 0 ∧ evalFunc (codeMat 132) M = 0) ∧ evalFunc (codeMat 68) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 196, 33, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s11_sourceU_le_actual :
    o451SourceU ⟨11, by omega⟩ ≤ o451ActualSourceSpan ⟨11, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 132, 37, 19, 10] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 299) ⊓ kerEvalFunc (codeMat 164) ⊓ kerEvalFunc (codeMat 64) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 299) M = 0 ∧ evalFunc (codeMat 164) M = 0) ∧ evalFunc (codeMat 64) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 132, 37, 19, 10] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s12_sourceU_le_actual :
    o451SourceU ⟨12, by omega⟩ ≤ o451ActualSourceSpan ⟨12, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 96, 19, 10, 5] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 271) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 96) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 96, 19, 10, 5] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s13_sourceU_le_actual :
    o451SourceU ⟨13, by omega⟩ ≤ o451ActualSourceSpan ⟨13, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 97, 19, 10, 5] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 303) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (((evalFunc (codeMat 303) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 96) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 97, 19, 10, 5] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s14_sourceU_le_actual :
    o451SourceU ⟨14, by omega⟩ ≤ o451ActualSourceSpan ⟨14, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 64, 17, 8, 2] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 273) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 4)) at hM
    change ((evalFunc (codeMat 273) M = 0 ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 4) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 64, 17, 8, 2] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s15_sourceU_le_actual :
    o451SourceU ⟨15, by omega⟩ ≤ o451ActualSourceSpan ⟨15, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 64, 16, 9, 3] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 4)) at hM
    change ((evalFunc (codeMat 267) M = 0 ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 4) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 64, 16, 9, 3] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s16_sourceU_le_actual :
    o451SourceU ⟨16, by omega⟩ ≤ o451ActualSourceSpan ⟨16, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 164, 96, 18, 10, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 132) ⊓ kerEvalFunc (codeMat 100) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 132) M = 0 ∧ evalFunc (codeMat 100) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 18, 10, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s17_sourceU_le_actual :
    o451SourceU ⟨17, by omega⟩ ≤ o451ActualSourceSpan ⟨17, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 100, 18, 10, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 164) ⊓ kerEvalFunc (codeMat 96) ⊓ kerEvalFunc (codeMat 26)) at hM
    change ((evalFunc (codeMat 164) M = 0 ∧ evalFunc (codeMat 96) M = 0) ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 100, 18, 10, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s18_sourceU_le_actual :
    o451SourceU ⟨18, by omega⟩ ≤ o451ActualSourceSpan ⟨18, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 32, 17, 8, 4, 2] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 273) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 64)) at hM
    change ((evalFunc (codeMat 273) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 32, 17, 8, 4, 2] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s19_sourceU_le_actual :
    o451SourceU ⟨19, by omega⟩ ≤ o451ActualSourceSpan ⟨19, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 32, 16, 9, 4, 3] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 267) ⊓ kerEvalFunc (codeMat 128) ⊓ kerEvalFunc (codeMat 64)) at hM
    change ((evalFunc (codeMat 267) M = 0 ∧ evalFunc (codeMat 128) M = 0) ∧ evalFunc (codeMat 64) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 32, 16, 9, 4, 3] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s20_sourceU_le_actual :
    o451SourceU ⟨20, by omega⟩ ≤ o451ActualSourceSpan ⟨20, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 129, 66, 34, 19, 10, 4] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 401) ⊓ kerEvalFunc (codeMat 122)) at hM
    change (evalFunc (codeMat 401) M = 0 ∧ evalFunc (codeMat 122) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 129, 66, 34, 19, 10, 4] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s21_sourceU_le_actual :
    o451SourceU ⟨21, by omega⟩ ≤ o451ActualSourceSpan ⟨21, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 130, 67, 35, 19, 10, 4] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 369) ⊓ kerEvalFunc (codeMat 250)) at hM
    change (evalFunc (codeMat 369) M = 0 ∧ evalFunc (codeMat 250) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 130, 67, 35, 19, 10, 4] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s22_sourceU_le_actual :
    o451SourceU ⟨22, by omega⟩ ≤ o451ActualSourceSpan ⟨22, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 131, 65, 32, 19, 10, 6] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 335) ⊓ kerEvalFunc (codeMat 158)) at hM
    change (evalFunc (codeMat 335) M = 0 ∧ evalFunc (codeMat 158) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 131, 65, 32, 19, 10, 6] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s23_sourceU_le_actual :
    o451SourceU ⟨23, by omega⟩ ≤ o451ActualSourceSpan ⟨23, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 130, 67, 34, 19, 10, 6] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 337) ⊓ kerEvalFunc (codeMat 254)) at hM
    change (evalFunc (codeMat 337) M = 0 ∧ evalFunc (codeMat 254) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 130, 67, 34, 19, 10, 6] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s24_sourceU_le_actual :
    o451SourceU ⟨24, by omega⟩ ≤ o451ActualSourceSpan ⟨24, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 130, 64, 33, 19, 10, 6] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 305) ⊓ kerEvalFunc (codeMat 158)) at hM
    change (evalFunc (codeMat 305) M = 0 ∧ evalFunc (codeMat 158) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 130, 64, 33, 19, 10, 6] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s25_sourceU_le_actual :
    o451SourceU ⟨25, by omega⟩ ≤ o451ActualSourceSpan ⟨25, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 67, 33, 19, 10, 6] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 303) ⊓ kerEvalFunc (codeMat 94)) at hM
    change (evalFunc (codeMat 303) M = 0 ∧ evalFunc (codeMat 94) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 67, 33, 19, 10, 6] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s26_sourceU_le_actual :
    o451SourceU ⟨26, by omega⟩ ≤ o451ActualSourceSpan ⟨26, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 131, 67, 35, 19, 10, 5] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 271) ⊓ kerEvalFunc (codeMat 250)) at hM
    change (evalFunc (codeMat 271) M = 0 ∧ evalFunc (codeMat 250) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 131, 67, 35, 19, 10, 5] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s27_sourceU_le_actual :
    o451SourceU ⟨27, by omega⟩ ≤ o451ActualSourceSpan ⟨27, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 131, 64, 34, 19, 10, 7] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 299) ⊓ kerEvalFunc (codeMat 190)) at hM
    change (evalFunc (codeMat 299) M = 0 ∧ evalFunc (codeMat 190) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 131, 64, 34, 19, 10, 7] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s28_sourceU_le_actual :
    o451SourceU ⟨28, by omega⟩ ≤ o451ActualSourceSpan ⟨28, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 68, 32, 18, 10, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (evalFunc (codeMat 196) M = 0 ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 32, 18, 10, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s29_sourceU_le_actual :
    o451SourceU ⟨29, by omega⟩ ≤ o451ActualSourceSpan ⟨29, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 68, 36, 18, 10, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 100) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (evalFunc (codeMat 100) M = 0 ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 36, 18, 10, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s30_sourceU_le_actual :
    o451SourceU ⟨30, by omega⟩ ≤ o451ActualSourceSpan ⟨30, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 160, 64, 18, 10, 4, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 26)) at hM
    change (evalFunc (codeMat 160) M = 0 ∧ evalFunc (codeMat 26) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 18, 10, 4, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s31_sourceU_le_actual :
    o451SourceU ⟨31, by omega⟩ ≤ o451ActualSourceSpan ⟨31, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 164, 68, 16, 8, 2, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 160) ⊓ kerEvalFunc (codeMat 100)) at hM
    change (evalFunc (codeMat 160) M = 0 ∧ evalFunc (codeMat 100) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 164, 68, 16, 8, 2, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s32_sourceU_le_actual :
    o451SourceU ⟨32, by omega⟩ ≤ o451ActualSourceSpan ⟨32, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 65, 33, 17, 8, 4, 2] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 369)) at hM
    change evalFunc (codeMat 369) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 65, 33, 17, 8, 4, 2] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s33_sourceU_le_actual :
    o451SourceU ⟨33, by omega⟩ ≤ o451ActualSourceSpan ⟨33, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 129, 64, 32, 17, 8, 5, 2] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 405)) at hM
    change evalFunc (codeMat 405) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 129, 64, 32, 17, 8, 5, 2] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s34_sourceU_le_actual :
    o451SourceU ⟨34, by omega⟩ ≤ o451ActualSourceSpan ⟨34, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 129, 65, 33, 17, 8, 5, 2] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 501)) at hM
    change evalFunc (codeMat 501) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 129, 65, 33, 17, 8, 5, 2] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s35_sourceU_le_actual :
    o451SourceU ⟨35, by omega⟩ ≤ o451ActualSourceSpan ⟨35, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 129, 65, 33, 16, 9, 4, 3] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 491)) at hM
    change evalFunc (codeMat 491) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 129, 65, 33, 16, 9, 4, 3] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s36_sourceU_le_actual :
    o451SourceU ⟨36, by omega⟩ ≤ o451ActualSourceSpan ⟨36, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 128, 65, 32, 16, 9, 5, 3] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 335)) at hM
    change evalFunc (codeMat 335) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 128, 65, 32, 16, 9, 5, 3] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s37_sourceU_le_actual :
    o451SourceU ⟨37, by omega⟩ ≤ o451ActualSourceSpan ⟨37, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 129, 64, 33, 16, 9, 5, 3] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 431)) at hM
    change evalFunc (codeMat 431) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 129, 64, 33, 16, 9, 5, 3] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s38_sourceU_le_actual :
    o451SourceU ⟨38, by omega⟩ ≤ o451ActualSourceSpan ⟨38, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 66, 34, 18, 10, 4, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 122)) at hM
    change evalFunc (codeMat 122) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 34, 18, 10, 4, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s39_sourceU_le_actual :
    o451SourceU ⟨39, by omega⟩ ≤ o451ActualSourceSpan ⟨39, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 66, 34, 18, 10, 4, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 250)) at hM
    change evalFunc (codeMat 250) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 34, 18, 10, 4, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s40_sourceU_le_actual :
    o451SourceU ⟨40, by omega⟩ ≤ o451ActualSourceSpan ⟨40, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 64, 32, 18, 10, 6, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 158)) at hM
    change evalFunc (codeMat 158) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 64, 32, 18, 10, 6, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s41_sourceU_le_actual :
    o451SourceU ⟨41, by omega⟩ ≤ o451ActualSourceSpan ⟨41, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 128, 66, 32, 18, 10, 6, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 94)) at hM
    change evalFunc (codeMat 94) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 32, 18, 10, 6, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s42_sourceU_le_actual :
    o451SourceU ⟨42, by omega⟩ ≤ o451ActualSourceSpan ⟨42, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 64, 34, 18, 10, 6, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 190)) at hM
    change evalFunc (codeMat 190) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 64, 34, 18, 10, 6, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

theorem o451s43_sourceU_le_actual :
    o451SourceU ⟨43, by omega⟩ ≤ o451ActualSourceSpan ⟨43, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 130, 66, 34, 18, 10, 6, 1] (o451BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 254)) at hM
    change evalFunc (codeMat 254) M = 0 at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 34, 18, 10, 6, 1] (o451BridgeMatCode M) hbool
  rwa [o451_codeMat_bridgeCode] at hspan

end QiushiMatmul
end
