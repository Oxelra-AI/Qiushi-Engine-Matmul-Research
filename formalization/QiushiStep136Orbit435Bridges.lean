import QiushiStep136Orbit435Defs

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem o435s0_sourceU_le_actual :
    o435SourceU ⟨0, by omega⟩ ≤ o435ActualSourceSpan ⟨0, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [327, 193, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 401)) at hM
    change ((((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 149) M = 0) ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 401) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [327, 193, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s1_sourceU_le_actual :
    o435SourceU ⟨1, by omega⟩ ≤ o435ActualSourceSpan ⟨1, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 161, 96, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 480)) at hM
    change (((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 26) M = 0) ∧ evalFunc (codeMat 4) M = 0) ∧ evalFunc (codeMat 480) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 161, 96, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s2_sourceU_le_actual :
    o435SourceU ⟨2, by omega⟩ ≤ o435ActualSourceSpan ⟨2, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [292, 133, 68, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 228) ⊓ kerEvalFunc (codeMat 288)) at hM
    change (((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 26) M = 0) ∧ evalFunc (codeMat 228) M = 0) ∧ evalFunc (codeMat 288) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 133, 68, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s3_sourceU_le_actual :
    o435SourceU ⟨3, by omega⟩ ≤ o435ActualSourceSpan ⟨3, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 165, 100, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 222) ⊓ kerEvalFunc (codeMat 282)) at hM
    change (((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 62) M = 0) ∧ evalFunc (codeMat 222) M = 0) ∧ evalFunc (codeMat 282) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 165, 100, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s4_sourceU_le_actual :
    o435SourceU ⟨4, by omega⟩ ≤ o435ActualSourceSpan ⟨4, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 163, 98, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 218)) at hM
    change (((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 4) M = 0) ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 218) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 163, 98, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s5_sourceU_le_actual :
    o435SourceU ⟨5, by omega⟩ ≤ o435ActualSourceSpan ⟨5, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [291, 167, 102, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 401)) at hM
    change (((evalFunc (codeMat 143) M = 0 ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 75) M = 0) ∧ evalFunc (codeMat 401) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [291, 167, 102, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s6_sourceU_le_actual :
    o435SourceU ⟨6, by omega⟩ ≤ o435ActualSourceSpan ⟨6, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 160, 97, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 433)) at hM
    change (((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 4) M = 0) ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 433) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 97, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s7_sourceU_le_actual :
    o435SourceU ⟨7, by omega⟩ ≤ o435ActualSourceSpan ⟨7, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 160, 97, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 224) ⊓ kerEvalFunc (codeMat 433)) at hM
    change (((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 4) M = 0) ∧ evalFunc (codeMat 224) M = 0) ∧ evalFunc (codeMat 433) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 160, 97, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s8_sourceU_le_actual :
    o435SourceU ⟨8, by omega⟩ ≤ o435ActualSourceSpan ⟨8, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [289, 132, 69, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 405)) at hM
    change (((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 181) M = 0) ∧ evalFunc (codeMat 196) M = 0) ∧ evalFunc (codeMat 405) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [289, 132, 69, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s9_sourceU_le_actual :
    o435SourceU ⟨9, by omega⟩ ≤ o435ActualSourceSpan ⟨9, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [295, 132, 69, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 282)) at hM
    change (((evalFunc (codeMat 149) M = 0 ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 75) M = 0) ∧ evalFunc (codeMat 282) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [295, 132, 69, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s10_sourceU_le_actual :
    o435SourceU ⟨10, by omega⟩ ≤ o435ActualSourceSpan ⟨10, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 164, 101, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 433)) at hM
    change (((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 149) M = 0) ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 433) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 164, 101, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s11_sourceU_le_actual :
    o435SourceU ⟨11, by omega⟩ ≤ o435ActualSourceSpan ⟨11, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 164, 101, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 405)) at hM
    change (((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 177) M = 0) ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 405) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 164, 101, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s12_sourceU_le_actual :
    o435SourceU ⟨12, by omega⟩ ≤ o435ActualSourceSpan ⟨12, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 134, 71, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 288)) at hM
    change (((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 149) M = 0) ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 288) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 134, 71, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s13_sourceU_le_actual :
    o435SourceU ⟨13, by omega⟩ ≤ o435ActualSourceSpan ⟨13, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 166, 103, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 433)) at hM
    change (((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 149) M = 0) ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 433) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 166, 103, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s14_sourceU_le_actual :
    o435SourceU ⟨14, by omega⟩ ≤ o435ActualSourceSpan ⟨14, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [129, 64, 17, 8, 2] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 4) M = 0) ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [129, 64, 17, 8, 2] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s15_sourceU_le_actual :
    o435SourceU ⟨15, by omega⟩ ≤ o435ActualSourceSpan ⟨15, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [128, 65, 16, 9, 3] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 4) M = 0 ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 75) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 65, 16, 9, 3] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s16_sourceU_le_actual :
    o435SourceU ⟨16, by omega⟩ ≤ o435ActualSourceSpan ⟨16, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [130, 66, 18, 10, 1] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 218) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 4) M = 0 ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 218) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [130, 66, 18, 10, 1] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s17_sourceU_le_actual :
    o435SourceU ⟨17, by omega⟩ ≤ o435ActualSourceSpan ⟨17, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [193, 34, 19, 10, 4] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [193, 34, 19, 10, 4] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s18_sourceU_le_actual :
    o435SourceU ⟨18, by omega⟩ ≤ o435ActualSourceSpan ⟨18, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [193, 33, 19, 10, 4] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 177) M = 0) ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [193, 33, 19, 10, 4] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s19_sourceU_le_actual :
    o435SourceU ⟨19, by omega⟩ ≤ o435ActualSourceSpan ⟨19, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [193, 34, 19, 10, 6] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 62) M = 0) ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [193, 34, 19, 10, 6] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s20_sourceU_le_actual :
    o435SourceU ⟨20, by omega⟩ ≤ o435ActualSourceSpan ⟨20, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [193, 33, 19, 10, 5] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 181) M = 0) ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [193, 33, 19, 10, 5] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s21_sourceU_le_actual :
    o435SourceU ⟨21, by omega⟩ ≤ o435ActualSourceSpan ⟨21, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [193, 35, 19, 10, 5] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 143) M = 0 ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [193, 35, 19, 10, 5] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s22_sourceU_le_actual :
    o435SourceU ⟨22, by omega⟩ ≤ o435ActualSourceSpan ⟨22, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [193, 32, 19, 10, 7] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 149) M = 0) ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [193, 32, 19, 10, 7] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s23_sourceU_le_actual :
    o435SourceU ⟨23, by omega⟩ ≤ o435ActualSourceSpan ⟨23, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [193, 35, 19, 10, 7] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 256)) at hM
    change (((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 181) M = 0) ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 256) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [193, 35, 19, 10, 7] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s24_sourceU_le_actual :
    o435SourceU ⟨24, by omega⟩ ≤ o435ActualSourceSpan ⟨24, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 132, 69, 32, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 196) ⊓ kerEvalFunc (codeMat 405)) at hM
    change ((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 196) M = 0) ∧ evalFunc (codeMat 405) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 132, 69, 32, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s25_sourceU_le_actual :
    o435SourceU ⟨25, by omega⟩ ≤ o435ActualSourceSpan ⟨25, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 134, 71, 36, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 395)) at hM
    change ((evalFunc (codeMat 62) M = 0 ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 395) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 134, 71, 36, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s26_sourceU_le_actual :
    o435SourceU ⟨26, by omega⟩ ≤ o435ActualSourceSpan ⟨26, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [261, 133, 68, 34, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 85) ⊓ kerEvalFunc (codeMat 401)) at hM
    change ((evalFunc (codeMat 58) M = 0 ∧ evalFunc (codeMat 85) M = 0) ∧ evalFunc (codeMat 401) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [261, 133, 68, 34, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s27_sourceU_le_actual :
    o435SourceU ⟨27, by omega⟩ ≤ o435ActualSourceSpan ⟨27, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 132, 69, 34, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 81) ⊓ kerEvalFunc (codeMat 405)) at hM
    change ((evalFunc (codeMat 58) M = 0 ∧ evalFunc (codeMat 81) M = 0) ∧ evalFunc (codeMat 405) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 69, 34, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s28_sourceU_le_actual :
    o435SourceU ⟨28, by omega⟩ ≤ o435ActualSourceSpan ⟨28, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 133, 68, 38, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 478)) at hM
    change ((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 58) M = 0) ∧ evalFunc (codeMat 478) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 133, 68, 38, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s29_sourceU_le_actual :
    o435SourceU ⟨29, by omega⟩ ≤ o435ActualSourceSpan ⟨29, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 135, 70, 38, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 250) ⊓ kerEvalFunc (codeMat 286)) at hM
    change ((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 250) M = 0) ∧ evalFunc (codeMat 286) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 135, 70, 38, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s30_sourceU_le_actual :
    o435SourceU ⟨30, by omega⟩ ≤ o435ActualSourceSpan ⟨30, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 135, 70, 33, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 30) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 218)) at hM
    change ((evalFunc (codeMat 30) M = 0 ∧ evalFunc (codeMat 177) M = 0) ∧ evalFunc (codeMat 218) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 135, 70, 33, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s31_sourceU_le_actual :
    o435SourceU ⟨31, by omega⟩ ≤ o435ActualSourceSpan ⟨31, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 134, 71, 37, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 113) ⊓ kerEvalFunc (codeMat 427)) at hM
    change ((evalFunc (codeMat 149) M = 0 ∧ evalFunc (codeMat 113) M = 0) ∧ evalFunc (codeMat 427) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 134, 71, 37, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s32_sourceU_le_actual :
    o435SourceU ⟨32, by omega⟩ ≤ o435ActualSourceSpan ⟨32, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [262, 135, 70, 35, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 331)) at hM
    change ((evalFunc (codeMat 143) M = 0 ∧ evalFunc (codeMat 177) M = 0) ∧ evalFunc (codeMat 331) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 135, 70, 35, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s33_sourceU_le_actual :
    o435SourceU ⟨33, by omega⟩ ≤ o435ActualSourceSpan ⟨33, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [263, 134, 71, 35, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 452)) at hM
    change ((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 181) M = 0) ∧ evalFunc (codeMat 452) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [263, 134, 71, 35, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s34_sourceU_le_actual :
    o435SourceU ⟨34, by omega⟩ ≤ o435ActualSourceSpan ⟨34, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [259, 133, 68, 39, 19, 10] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 228) ⊓ kerEvalFunc (codeMat 433)) at hM
    change ((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 228) M = 0) ∧ evalFunc (codeMat 433) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [259, 133, 68, 39, 19, 10] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s35_sourceU_le_actual :
    o435SourceU ⟨35, by omega⟩ ≤ o435ActualSourceSpan ⟨35, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [291, 161, 96, 19, 10, 4] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 113) ⊓ kerEvalFunc (codeMat 401)) at hM
    change ((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 113) M = 0) ∧ evalFunc (codeMat 401) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [291, 161, 96, 19, 10, 4] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s36_sourceU_le_actual :
    o435SourceU ⟨36, by omega⟩ ≤ o435ActualSourceSpan ⟨36, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [291, 162, 99, 19, 10, 4] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 337)) at hM
    change ((evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 177) M = 0) ∧ evalFunc (codeMat 337) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [291, 162, 99, 19, 10, 4] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s37_sourceU_le_actual :
    o435SourceU ⟨37, by omega⟩ ≤ o435ActualSourceSpan ⟨37, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 161, 96, 19, 10, 6] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 30) ⊓ kerEvalFunc (codeMat 224) ⊓ kerEvalFunc (codeMat 401)) at hM
    change ((evalFunc (codeMat 30) M = 0 ∧ evalFunc (codeMat 224) M = 0) ∧ evalFunc (codeMat 401) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 161, 96, 19, 10, 6] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s38_sourceU_le_actual :
    o435SourceU ⟨38, by omega⟩ ≤ o435ActualSourceSpan ⟨38, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 160, 97, 19, 10, 5] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 85)) at hM
    change ((evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 181) M = 0) ∧ evalFunc (codeMat 85) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 19, 10, 5] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s39_sourceU_le_actual :
    o435SourceU ⟨39, by omega⟩ ≤ o435ActualSourceSpan ⟨39, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [291, 163, 98, 19, 10, 7] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 62) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 405)) at hM
    change ((evalFunc (codeMat 62) M = 0 ∧ evalFunc (codeMat 75) M = 0) ∧ evalFunc (codeMat 405) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [291, 163, 98, 19, 10, 7] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s40_sourceU_le_actual :
    o435SourceU ⟨40, by omega⟩ ≤ o435ActualSourceSpan ⟨40, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [291, 160, 97, 19, 10, 7] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 286)) at hM
    change ((evalFunc (codeMat 181) M = 0 ∧ evalFunc (codeMat 75) M = 0) ∧ evalFunc (codeMat 286) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [291, 160, 97, 19, 10, 7] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s41_sourceU_le_actual :
    o435SourceU ⟨41, by omega⟩ ≤ o435ActualSourceSpan ⟨41, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [261, 128, 65, 17, 8, 2] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 85) ⊓ kerEvalFunc (codeMat 260)) at hM
    change ((evalFunc (codeMat 32) M = 0 ∧ evalFunc (codeMat 85) M = 0) ∧ evalFunc (codeMat 260) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [261, 128, 65, 17, 8, 2] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s42_sourceU_le_actual :
    o435SourceU ⟨42, by omega⟩ ≤ o435ActualSourceSpan ⟨42, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [293, 129, 64, 16, 9, 3] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 395)) at hM
    change ((evalFunc (codeMat 143) M = 0 ∧ evalFunc (codeMat 171) M = 0) ∧ evalFunc (codeMat 395) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [293, 129, 64, 16, 9, 3] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s43_sourceU_le_actual :
    o435SourceU ⟨43, by omega⟩ ≤ o435ActualSourceSpan ⟨43, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 128, 64, 18, 10, 1] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 4) ⊓ kerEvalFunc (codeMat 32) ⊓ kerEvalFunc (codeMat 282)) at hM
    change ((evalFunc (codeMat 4) M = 0 ∧ evalFunc (codeMat 32) M = 0) ∧ evalFunc (codeMat 282) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 18, 10, 1] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s44_sourceU_le_actual :
    o435SourceU ⟨44, by omega⟩ ≤ o435ActualSourceSpan ⟨44, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [259, 193, 34, 19, 10, 4] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 401)) at hM
    change ((evalFunc (codeMat 171) M = 0 ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 401) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [259, 193, 34, 19, 10, 4] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s45_sourceU_le_actual :
    o435SourceU ⟨45, by omega⟩ ≤ o435ActualSourceSpan ⟨45, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [259, 193, 33, 19, 10, 4] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 282)) at hM
    change ((evalFunc (codeMat 171) M = 0 ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 282) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [259, 193, 33, 19, 10, 4] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s46_sourceU_le_actual :
    o435SourceU ⟨46, by omega⟩ ≤ o435ActualSourceSpan ⟨46, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [322, 193, 35, 19, 10, 4] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 75) ⊓ kerEvalFunc (codeMat 395)) at hM
    change ((evalFunc (codeMat 177) M = 0 ∧ evalFunc (codeMat 75) M = 0) ∧ evalFunc (codeMat 395) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [322, 193, 35, 19, 10, 4] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s47_sourceU_le_actual :
    o435SourceU ⟨47, by omega⟩ ≤ o435ActualSourceSpan ⟨47, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [322, 193, 34, 19, 10, 6] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 254) ⊓ kerEvalFunc (codeMat 318)) at hM
    change ((evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 254) M = 0) ∧ evalFunc (codeMat 318) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [322, 193, 34, 19, 10, 6] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s48_sourceU_le_actual :
    o435SourceU ⟨48, by omega⟩ ≤ o435ActualSourceSpan ⟨48, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [322, 193, 33, 19, 10, 6] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 177) ⊓ kerEvalFunc (codeMat 222) ⊓ kerEvalFunc (codeMat 286)) at hM
    change ((evalFunc (codeMat 177) M = 0 ∧ evalFunc (codeMat 222) M = 0) ∧ evalFunc (codeMat 286) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [322, 193, 33, 19, 10, 6] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s49_sourceU_le_actual :
    o435SourceU ⟨49, by omega⟩ ≤ o435ActualSourceSpan ⟨49, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [323, 193, 32, 19, 10, 5] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 218) ⊓ kerEvalFunc (codeMat 282)) at hM
    change ((evalFunc (codeMat 143) M = 0 ∧ evalFunc (codeMat 218) M = 0) ∧ evalFunc (codeMat 282) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [323, 193, 32, 19, 10, 5] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s50_sourceU_le_actual :
    o435SourceU ⟨50, by omega⟩ ≤ o435ActualSourceSpan ⟨50, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 193, 33, 19, 10, 5] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 181) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 282)) at hM
    change ((evalFunc (codeMat 181) M = 0 ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 282) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 193, 33, 19, 10, 5] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s51_sourceU_le_actual :
    o435SourceU ⟨51, by omega⟩ ≤ o435ActualSourceSpan ⟨51, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [323, 193, 35, 19, 10, 5] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 250) ⊓ kerEvalFunc (codeMat 314)) at hM
    change ((evalFunc (codeMat 143) M = 0 ∧ evalFunc (codeMat 250) M = 0) ∧ evalFunc (codeMat 314) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [323, 193, 35, 19, 10, 5] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s52_sourceU_le_actual :
    o435SourceU ⟨52, by omega⟩ ≤ o435ActualSourceSpan ⟨52, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [258, 193, 32, 19, 10, 7] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 192) ⊓ kerEvalFunc (codeMat 395)) at hM
    change ((evalFunc (codeMat 149) M = 0 ∧ evalFunc (codeMat 192) M = 0) ∧ evalFunc (codeMat 395) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 193, 32, 19, 10, 7] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s53_sourceU_le_actual :
    o435SourceU ⟨53, by omega⟩ ≤ o435ActualSourceSpan ⟨53, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [323, 193, 34, 19, 10, 7] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 171) ⊓ kerEvalFunc (codeMat 85) ⊓ kerEvalFunc (codeMat 405)) at hM
    change ((evalFunc (codeMat 171) M = 0 ∧ evalFunc (codeMat 85) M = 0) ∧ evalFunc (codeMat 405) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [323, 193, 34, 19, 10, 7] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s54_sourceU_le_actual :
    o435SourceU ⟨54, by omega⟩ ≤ o435ActualSourceSpan ⟨54, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [259, 130, 67, 32, 19, 10, 6] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 143) ⊓ kerEvalFunc (codeMat 337)) at hM
    change (evalFunc (codeMat 143) M = 0 ∧ evalFunc (codeMat 337) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [259, 130, 67, 32, 19, 10, 6] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s55_sourceU_le_actual :
    o435SourceU ⟨55, by omega⟩ ≤ o435ActualSourceSpan ⟨55, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 133, 68, 36, 17, 8, 2] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 145) ⊓ kerEvalFunc (codeMat 484)) at hM
    change (evalFunc (codeMat 145) M = 0 ∧ evalFunc (codeMat 484) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 133, 68, 36, 17, 8, 2] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s56_sourceU_le_actual :
    o435SourceU ⟨56, by omega⟩ ≤ o435ActualSourceSpan ⟨56, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [257, 133, 68, 37, 17, 8, 2] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 228) ⊓ kerEvalFunc (codeMat 433)) at hM
    change (evalFunc (codeMat 228) M = 0 ∧ evalFunc (codeMat 433) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 133, 68, 37, 17, 8, 2] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s57_sourceU_le_actual :
    o435SourceU ⟨57, by omega⟩ ≤ o435ActualSourceSpan ⟨57, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 69, 37, 17, 8, 2] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 149) ⊓ kerEvalFunc (codeMat 113)) at hM
    change (evalFunc (codeMat 149) M = 0 ∧ evalFunc (codeMat 113) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 69, 37, 17, 8, 2] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s58_sourceU_le_actual :
    o435SourceU ⟨58, by omega⟩ ≤ o435ActualSourceSpan ⟨58, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 132, 68, 32, 18, 10, 1] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 26) ⊓ kerEvalFunc (codeMat 196)) at hM
    change (evalFunc (codeMat 26) M = 0 ∧ evalFunc (codeMat 196) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 32, 18, 10, 1] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s59_sourceU_le_actual :
    o435SourceU ⟨59, by omega⟩ ≤ o435ActualSourceSpan ⟨59, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 134, 70, 32, 18, 10, 1] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 30) ⊓ kerEvalFunc (codeMat 218)) at hM
    change (evalFunc (codeMat 30) M = 0 ∧ evalFunc (codeMat 218) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 134, 70, 32, 18, 10, 1] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s60_sourceU_le_actual :
    o435SourceU ⟨60, by omega⟩ ≤ o435ActualSourceSpan ⟨60, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [260, 132, 68, 34, 18, 10, 1] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 58) ⊓ kerEvalFunc (codeMat 452)) at hM
    change (evalFunc (codeMat 58) M = 0 ∧ evalFunc (codeMat 452) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 34, 18, 10, 1] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s61_sourceU_le_actual :
    o435SourceU ⟨61, by omega⟩ ≤ o435ActualSourceSpan ⟨61, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [288, 161, 96, 16, 9, 4, 3] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 139) ⊓ kerEvalFunc (codeMat 480)) at hM
    change (evalFunc (codeMat 139) M = 0 ∧ evalFunc (codeMat 480) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 161, 96, 16, 9, 4, 3] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

theorem o435s62_sourceU_le_actual :
    o435SourceU ⟨62, by omega⟩ ≤ o435ActualSourceSpan ⟨62, by omega⟩ := by
  intro M hM
  have hbool : spanContainsCodeCore [256, 160, 97, 16, 9, 5, 3] (o435BridgeMatCode M) = true := by
    change M ∈ (kerEvalFunc (codeMat 175) ⊓ kerEvalFunc (codeMat 79)) at hM
    change (evalFunc (codeMat 175) M = 0 ∧ evalFunc (codeMat 79) M = 0) at hM
    revert M
    decide
  have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 97, 16, 9, 5, 3] (o435BridgeMatCode M) hbool
  rwa [o435_codeMat_bridgeCode] at hspan

end QiushiMatmul
end
