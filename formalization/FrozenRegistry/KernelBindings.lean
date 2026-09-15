import FrozenRegistry.Bridge
import FrozenRegistry.AdditionalSources

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace QiushiMatmul.FrozenRegistry.Kernel

theorem bound000 : QuotientRankAtLeast (spanCodes [68, 18, 10, 1]) 17 := by
  have h := QiushiMatmul.step108o450s0Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17 + QiushiMatmul.codeMat 11))) 17 at h
  have hgen : ∀ c ∈ [68, 18, 10, 1], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17 + QiushiMatmul.codeMat 11))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound001 : QuotientRankAtLeast (spanCodes [128, 65, 16, 9, 3]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (15 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [128, 65, 16, 9, 3], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound002 : QuotientRankAtLeast (spanCodes [129, 64, 17, 8, 2]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (14 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [129, 64, 17, 8, 2], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound003 : QuotientRankAtLeast (spanCodes [130, 66, 18, 10, 1]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (16 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [130, 66, 18, 10, 1], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound004 : QuotientRankAtLeast (spanCodes [160, 68, 16, 8, 2, 1]) 15 := by
  have h := QiushiMatmul.step99o377s0Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) 15 at h
  have hgen : ∀ c ∈ [160, 68, 16, 8, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound005 : QuotientRankAtLeast (spanCodes [161, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s1Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17 + QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 17))) 17 at h
  have hgen : ∀ c ∈ [161, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17 + QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 17))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound006 : QuotientRankAtLeast (spanCodes [193, 32, 19, 10, 7]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (22 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [193, 32, 19, 10, 7], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound007 : QuotientRankAtLeast (spanCodes [193, 33, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (18 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [193, 33, 19, 10, 4], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound008 : QuotientRankAtLeast (spanCodes [193, 33, 19, 10, 5]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (20 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [193, 33, 19, 10, 5], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound009 : QuotientRankAtLeast (spanCodes [193, 34, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (17 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [193, 34, 19, 10, 4], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound010 : QuotientRankAtLeast (spanCodes [193, 34, 19, 10, 6]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (19 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [193, 34, 19, 10, 6], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound011 : QuotientRankAtLeast (spanCodes [193, 35, 19, 10, 5]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (21 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [193, 35, 19, 10, 5], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound012 : QuotientRankAtLeast (spanCodes [193, 35, 19, 10, 7]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (23 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) 15 at h
  have hgen : ∀ c ∈ [193, 35, 19, 10, 7], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound013 : QuotientRankAtLeast (spanCodes [256, 32, 16, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o120s4Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 32, 16, 12, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound014 : QuotientRankAtLeast (spanCodes [256, 68, 16, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o150s7Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) 12 at h
  have hgen : ∀ c ∈ [256, 68, 16, 8, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound015 : QuotientRankAtLeast (spanCodes [256, 68, 32, 20, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o34s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84))) 12 at h
  have hgen : ∀ c ∈ [256, 68, 32, 20, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound016 : QuotientRankAtLeast (spanCodes [256, 68, 36, 20, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o34s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84 + QiushiMatmul.codeMat 32))) 12 at h
  have hgen : ∀ c ∈ [256, 68, 36, 20, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84 + QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound017 : QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 17, 8, 5, 2]) 9 := by
  have h := QiushiMatmul.step108o450s16Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17 + QiushiMatmul.codeMat 68)) 9 at h
  have hgen : ∀ c ∈ [256, 128, 65, 32, 17, 8, 5, 2], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17 + QiushiMatmul.codeMat 68)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound018 : QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 16, 12, 1]) 12 := by
  have h := QiushiMatmul.step99o231s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 128, 66, 32, 16, 12, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound019 : QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  have h := QiushiMatmul.step81o17s1Seed2
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 94)) 9 at h
  have hgen : ∀ c ∈ [256, 128, 66, 32, 18, 10, 6, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 94)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound020 : QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 6, 1]) 9 := by
  have h := QiushiMatmul.step99o69s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 100 + QiushiMatmul.codeMat 10)) 9 at h
  have hgen : ∀ c ∈ [256, 128, 66, 34, 16, 10, 6, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 100 + QiushiMatmul.codeMat 10)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound021 : QuotientRankAtLeast (spanCodes [256, 128, 68, 20, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o34s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) 12 at h
  have hgen : ∀ c ∈ [256, 128, 68, 20, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound022 : QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  have h := QiushiMatmul.step99o76s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84)) 9 at h
  have hgen : ∀ c ∈ [256, 128, 68, 32, 20, 8, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound023 : QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 12, 2, 1]) 9 := by
  have h := QiushiMatmul.step81o16s2Seed1
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 92)) 9 at h
  have hgen : ∀ c ∈ [256, 128, 68, 32, 20, 12, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 92)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound024 : QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o69s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 100) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 128, 68, 36, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 100) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound025 : QuotientRankAtLeast (spanCodes [256, 128, 80, 32, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o56s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 80) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 128, 80, 32, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 80) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound026 : QuotientRankAtLeast (spanCodes [256, 128, 96, 16, 10, 4, 1]) 12 := by
  have h := QiushiMatmul.step99o77s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 128, 96, 16, 10, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound027 : QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 9, 4, 3]) 9 := by
  have h := QiushiMatmul.step108o450s15Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 11)) 9 at h
  have hgen : ∀ c ∈ [256, 129, 64, 33, 16, 9, 4, 3], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 11)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound028 : QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 8, 4, 2]) 9 := by
  have h := QiushiMatmul.step108o450s10Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 17)) 9 at h
  have hgen : ∀ c ∈ [256, 129, 64, 33, 17, 8, 4, 2], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 17)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound029 : QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 16, 9, 5, 3]) 9 := by
  have h := QiushiMatmul.step108o450s13Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 11)) 9 at h
  have hgen : ∀ c ∈ [256, 129, 65, 33, 16, 9, 5, 3], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 11)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound030 : QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 16, 10, 6, 1]) 9 := by
  have h := QiushiMatmul.step99o69s5Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 10)) 9 at h
  have hgen : ∀ c ∈ [256, 130, 64, 32, 16, 10, 6, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 10)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound031 : QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 16, 10, 6, 1]) 9 := by
  have h := QiushiMatmul.step99o67s3Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 110)) 9 at h
  have hgen : ∀ c ∈ [256, 130, 66, 32, 16, 10, 6, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 110)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound032 : QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 10, 4, 1]) 9 := by
  have h := QiushiMatmul.step99o69s6Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 100 + QiushiMatmul.codeMat 10)) 9 at h
  have hgen : ∀ c ∈ [256, 130, 66, 34, 16, 10, 4, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 100 + QiushiMatmul.codeMat 10)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound033 : QuotientRankAtLeast (spanCodes [256, 130, 68, 38, 16, 14, 1]) 12 := by
  have h := QiushiMatmul.step99o231s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 34 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 34 + QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 130, 68, 38, 16, 14, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 34 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 34 + QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound034 : QuotientRankAtLeast (spanCodes [256, 130, 82, 50, 10, 6, 1]) 12 := by
  have h := QiushiMatmul.step99o217s9Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112))) 12 at h
  have hgen : ∀ c ∈ [256, 130, 82, 50, 10, 6, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound035 : QuotientRankAtLeast (spanCodes [256, 130, 96, 20, 10, 1]) 15 := by
  have h := QiushiMatmul.step99o237s0Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) 15 at h
  have hgen : ∀ c ∈ [256, 130, 96, 20, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound036 : QuotientRankAtLeast (spanCodes [256, 132, 32, 16, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o55s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 32, 16, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound037 : QuotientRankAtLeast (spanCodes [256, 132, 32, 22, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o196s3Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) 14 at h
  have hgen : ∀ c ∈ [256, 132, 32, 22, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound038 : QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o69s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 64, 32, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound039 : QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 16, 12, 2, 1]) 9 := by
  have h := QiushiMatmul.step81o16s2Seed0
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140)) 9 at h
  have hgen : ∀ c ∈ [256, 132, 64, 32, 16, 12, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound040 : QuotientRankAtLeast (spanCodes [256, 132, 66, 34, 22, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o217s8Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 66, 34, 22, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound041 : QuotientRankAtLeast (spanCodes [256, 132, 68, 20, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o34s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 84) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 68, 20, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 84) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound042 : QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o68s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 68, 32, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound043 : QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 18, 10, 1]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (58 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 68, 32, 18, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound044 : QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 20, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o82s4Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 68, 36, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound045 : QuotientRankAtLeast (spanCodes [256, 132, 69, 37, 17, 8, 2]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (57 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 113))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 69, 37, 17, 8, 2], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 113))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound046 : QuotientRankAtLeast (spanCodes [256, 132, 80, 36, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o56s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 80))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 80, 36, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 80))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound047 : QuotientRankAtLeast (spanCodes [256, 132, 96, 16, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o231s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 34))) 12 at h
  have hgen : ∀ c ∈ [256, 132, 96, 16, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 34))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound048 : QuotientRankAtLeast (spanCodes [256, 134, 70, 32, 18, 10, 1]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (59 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 30) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218))) 12 at h
  have hgen : ∀ c ∈ [256, 134, 70, 32, 18, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 30) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound049 : QuotientRankAtLeast (spanCodes [256, 134, 70, 36, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o231s5Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 34 + QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 134, 70, 36, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 34 + QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound050 : QuotientRankAtLeast (spanCodes [256, 135, 70, 33, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (30 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 30) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218))) 15 at h
  have hgen : ∀ c ∈ [256, 135, 70, 33, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 30) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound051 : QuotientRankAtLeast (spanCodes [256, 136, 64, 34, 16, 4, 1]) 12 := by
  have h := QiushiMatmul.step99o231s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 34))) 12 at h
  have hgen : ∀ c ∈ [256, 136, 64, 34, 16, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 34))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound052 : QuotientRankAtLeast (spanCodes [256, 136, 68, 32, 16, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o144s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 136) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) 12 at h
  have hgen : ∀ c ∈ [256, 136, 68, 32, 16, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 136) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound053 : QuotientRankAtLeast (spanCodes [256, 138, 72, 42, 16, 6, 1]) 12 := by
  have h := QiushiMatmul.step99o231s4Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 34) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 138, 72, 42, 16, 6, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 34) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 66 + QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound054 : QuotientRankAtLeast (spanCodes [256, 144, 64, 48, 8, 4, 2, 1]) 6 := by
  have h := QiushiMatmul.seed_ker_176
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 176)) 6 at h
  have hgen : ∀ c ∈ [256, 144, 64, 48, 8, 4, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 176)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound055 : QuotientRankAtLeast (spanCodes [256, 144, 80, 32, 8, 4, 2, 1]) 6 := by
  have h := QiushiMatmul.step81o16s2Seed2
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 208)) 6 at h
  have hgen : ∀ c ∈ [256, 144, 80, 32, 8, 4, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 208)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound056 : QuotientRankAtLeast (spanCodes [256, 144, 80, 48, 8, 4, 2, 1]) 6 := by
  have h := QiushiMatmul.step99o56s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 80)) 6 at h
  have hgen : ∀ c ∈ [256, 144, 80, 48, 8, 4, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 80)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound057 : QuotientRankAtLeast (spanCodes [256, 148, 80, 32, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step81o16s2Pair_lb
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 208))) 12 at h
  have hgen : ∀ c ∈ [256, 148, 80, 32, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 208))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound058 : QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 8, 4, 2, 1]) 6 := by
  have h := QiushiMatmul.step99o34s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 32)) 6 at h
  have hgen : ∀ c ∈ [256, 160, 64, 16, 8, 4, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 32)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound059 : QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 10, 4, 1]) 12 := by
  have h := QiushiMatmul.step99o65s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 160, 64, 16, 10, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound060 : QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o56s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 160, 64, 16, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound061 : QuotientRankAtLeast (spanCodes [256, 160, 68, 20, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o56s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 80 + QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [256, 160, 68, 20, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 80 + QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound062 : QuotientRankAtLeast (spanCodes [256, 160, 96, 16, 10, 4, 1]) 12 := by
  have h := QiushiMatmul.step99o69s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 100) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [256, 160, 96, 16, 10, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132 + QiushiMatmul.codeMat 100) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound063 : QuotientRankAtLeast (spanCodes [256, 160, 97, 16, 9, 5, 3]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (62 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 175) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 79))) 12 at h
  have hgen : ∀ c ∈ [256, 160, 97, 16, 9, 5, 3], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 175) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 79))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound064 : QuotientRankAtLeast (spanCodes [256, 160, 97, 19, 10, 5]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (38 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85))) 15 at h
  have hgen : ∀ c ∈ [256, 160, 97, 19, 10, 5], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound065 : QuotientRankAtLeast (spanCodes [256, 161, 65, 19, 10, 5]) 15 := by
  have h := QiushiMatmul.step99o377s2Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [256, 161, 65, 19, 10, 5], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound066 : QuotientRankAtLeast (spanCodes [256, 163, 98, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (4 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218))) 15 at h
  have hgen : ∀ c ∈ [256, 163, 98, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound067 : QuotientRankAtLeast (spanCodes [256, 164, 96, 16, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o69s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 100))) 12 at h
  have hgen : ∀ c ∈ [256, 164, 96, 16, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 132) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 100))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound068 : QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 16, 9, 4, 3]) 9 := by
  have h := QiushiMatmul.step108o450s12Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 11)) 9 at h
  have hgen : ∀ c ∈ [257, 128, 64, 32, 16, 9, 4, 3], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 11)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound069 : QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 17, 8, 4, 2]) 9 := by
  have h := QiushiMatmul.step108o450s17Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 17)) 9 at h
  have hgen : ∀ c ∈ [257, 128, 64, 32, 17, 8, 4, 2], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 17)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound070 : QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 16, 9, 5, 3]) 9 := by
  have h := QiushiMatmul.step108o450s14Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 11)) 9 at h
  have hgen : ∀ c ∈ [257, 128, 65, 32, 16, 9, 5, 3], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 11)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound071 : QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 17, 8, 5, 2]) 9 := by
  have h := QiushiMatmul.step108o450s11Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 17 +
  QiushiMatmul.codeMat 68)) 9 at h
  have hgen : ∀ c ∈ [257, 129, 65, 33, 17, 8, 5, 2], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 17 +
  QiushiMatmul.codeMat 68)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound072 : QuotientRankAtLeast (spanCodes [257, 132, 69, 32, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (24 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) 15 at h
  have hgen : ∀ c ∈ [257, 132, 69, 32, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound073 : QuotientRankAtLeast (spanCodes [257, 133, 68, 37, 17, 8, 2]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (56 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 228) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) 12 at h
  have hgen : ∀ c ∈ [257, 133, 68, 37, 17, 8, 2], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 228) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound074 : QuotientRankAtLeast (spanCodes [257, 160, 97, 19, 10]) 16 := by
  have h := QiushiMatmul.o435_dispatch_hSource (7 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 224)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) 16 at h
  have hgen : ∀ c ∈ [257, 160, 97, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 224)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound075 : QuotientRankAtLeast (spanCodes [257, 161, 64, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.step99o377s3Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [257, 161, 64, 19, 10, 4], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound076 : QuotientRankAtLeast (spanCodes [257, 161, 96, 19, 10, 6]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (37 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 30) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 224)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) 15 at h
  have hgen : ∀ c ∈ [257, 161, 96, 19, 10, 6], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 30) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 224)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound077 : QuotientRankAtLeast (spanCodes [258, 64, 16, 10, 4, 1]) 14 := by
  have h := QiushiMatmul.step99o150s2Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) 14 at h
  have hgen : ∀ c ∈ [258, 64, 16, 10, 4, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound078 : QuotientRankAtLeast (spanCodes [258, 68, 34, 16, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o150s3Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) 14 at h
  have hgen : ∀ c ∈ [258, 68, 34, 16, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound079 : QuotientRankAtLeast (spanCodes [258, 68, 36, 16, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o150s4Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 32))) 14 at h
  have hgen : ∀ c ∈ [258, 68, 36, 16, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound080 : QuotientRankAtLeast (spanCodes [258, 128, 32, 16, 10, 4, 1]) 12 := by
  have h := QiushiMatmul.step99o196s7Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) 12 at h
  have hgen : ∀ c ∈ [258, 128, 32, 16, 10, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound081 : QuotientRankAtLeast (spanCodes [258, 128, 64, 18, 10, 1]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (43 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) 15 at h
  have hgen : ∀ c ∈ [258, 128, 64, 18, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound082 : QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  have h := QiushiMatmul.step81o17s0Seed1
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266)) 9 at h
  have hgen : ∀ c ∈ [258, 128, 64, 32, 16, 10, 4, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound083 : QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 6, 1]) 9 := by
  have h := QiushiMatmul.step99o150s8Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 68)) 9 at h
  have hgen : ∀ c ∈ [258, 128, 66, 32, 16, 10, 6, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 68)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound084 : QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 18, 10, 6, 1]) 9 := by
  have h := QiushiMatmul.step99o77s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 10)) 9 at h
  have hgen : ∀ c ∈ [258, 128, 66, 34, 18, 10, 6, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 10)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound085 : QuotientRankAtLeast (spanCodes [258, 128, 82, 50, 10, 4, 1]) 12 := by
  have h := QiushiMatmul.step99o217s11Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112))) 12 at h
  have hgen : ∀ c ∈ [258, 128, 82, 50, 10, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound086 : QuotientRankAtLeast (spanCodes [258, 128, 96, 20, 8, 1]) 14 := by
  have h := QiushiMatmul.step99o237s9Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) 14 at h
  have hgen : ∀ c ∈ [258, 128, 96, 20, 8, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound087 : QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) 9 := by
  have h := QiushiMatmul.step99o67s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 160)) 9 at h
  have hgen : ∀ c ∈ [258, 130, 64, 34, 16, 10, 4, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 160)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound088 : QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 10, 6, 1]) 9 := by
  have h := QiushiMatmul.step99o65s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324 + QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 10)) 9 at h
  have hgen : ∀ c ∈ [258, 130, 66, 34, 16, 10, 6, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324 + QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 10)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound089 : QuotientRankAtLeast (spanCodes [258, 130, 68, 16, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o150s5Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) 14 at h
  have hgen : ∀ c ∈ [258, 130, 68, 16, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound090 : QuotientRankAtLeast (spanCodes [258, 132, 64, 32, 22, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o217s10Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148))) 12 at h
  have hgen : ∀ c ∈ [258, 132, 64, 32, 22, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound091 : QuotientRankAtLeast (spanCodes [258, 132, 68, 16, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o150s6Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) 14 at h
  have hgen : ∀ c ∈ [258, 132, 68, 16, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound092 : QuotientRankAtLeast (spanCodes [258, 134, 68, 34, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o68s4Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196))) 12 at h
  have hgen : ∀ c ∈ [258, 134, 68, 34, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound093 : QuotientRankAtLeast (spanCodes [258, 134, 70, 38, 20, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o82s5Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244))) 12 at h
  have hgen : ∀ c ∈ [258, 134, 70, 38, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound094 : QuotientRankAtLeast (spanCodes [258, 134, 71, 37, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (31 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 113)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 427))) 15 at h
  have hgen : ∀ c ∈ [258, 134, 71, 37, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 113)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 427))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound095 : QuotientRankAtLeast (spanCodes [258, 161, 67, 19, 10, 7]) 15 := by
  have h := QiushiMatmul.step99o377s4Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [258, 161, 67, 19, 10, 7], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound096 : QuotientRankAtLeast (spanCodes [258, 162, 68, 16, 10, 1]) 15 := by
  have h := QiushiMatmul.step99o150s0Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) 15 at h
  have hgen : ∀ c ∈ [258, 162, 68, 16, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound097 : QuotientRankAtLeast (spanCodes [258, 164, 68, 16, 10, 1]) 15 := by
  have h := QiushiMatmul.step99o150s1Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 32))) 15 at h
  have hgen : ∀ c ∈ [258, 164, 68, 16, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 32))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound098 : QuotientRankAtLeast (spanCodes [258, 193, 32, 19, 10, 7]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (52 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) 15 at h
  have hgen : ∀ c ∈ [258, 193, 32, 19, 10, 7], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound099 : QuotientRankAtLeast (spanCodes [258, 193, 33, 19, 10, 5]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (50 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) 15 at h
  have hgen : ∀ c ∈ [258, 193, 33, 19, 10, 5], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound100 : QuotientRankAtLeast (spanCodes [259, 130, 67, 32, 19, 10, 6]) 14 := by
  have h := QiushiMatmul.o435_dispatch_hSource (54 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 337))) 14 at h
  have hgen : ∀ c ∈ [259, 130, 67, 32, 19, 10, 6], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 337))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound101 : QuotientRankAtLeast (spanCodes [259, 133, 68, 39, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (34 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 228)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) 15 at h
  have hgen : ∀ c ∈ [259, 133, 68, 39, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 228)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound102 : QuotientRankAtLeast (spanCodes [259, 161, 66, 19, 10, 6]) 15 := by
  have h := QiushiMatmul.step99o377s5Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43))) 15 at h
  have hgen : ∀ c ∈ [259, 161, 66, 19, 10, 6], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound103 : QuotientRankAtLeast (spanCodes [259, 193, 33, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (45 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) 15 at h
  have hgen : ∀ c ∈ [259, 193, 33, 19, 10, 4], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound104 : QuotientRankAtLeast (spanCodes [259, 193, 34, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (44 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) 15 at h
  have hgen : ∀ c ∈ [259, 193, 34, 19, 10, 4], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 192)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound105 : QuotientRankAtLeast (spanCodes [260, 32, 20, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o120s5Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) 12 at h
  have hgen : ∀ c ∈ [260, 32, 20, 12, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound106 : QuotientRankAtLeast (spanCodes [260, 128, 64, 32, 20, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o82s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [260, 128, 64, 32, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound107 : QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o65s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [260, 128, 68, 32, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound108 : QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  have h := QiushiMatmul.step81o17s2Seed0
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 340)) 9 at h
  have hgen : ∀ c ∈ [260, 128, 68, 32, 20, 8, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 340)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound109 : QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 16, 10, 1]) 9 := by
  have h := QiushiMatmul.step99o68s6Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 9 at h
  have hgen : ∀ c ∈ [260, 128, 68, 36, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound110 : QuotientRankAtLeast (spanCodes [260, 128, 70, 38, 20, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o77s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 10))) 14 at h
  have hgen : ∀ c ∈ [260, 128, 70, 38, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound111 : QuotientRankAtLeast (spanCodes [260, 128, 96, 20, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o77s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) 12 at h
  have hgen : ∀ c ∈ [260, 128, 96, 20, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound112 : QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 20, 12, 2, 1]) 9 := by
  have h := QiushiMatmul.step99o55s4Dispatch
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 140)) 9 at h
  have hgen : ∀ c ∈ [260, 132, 64, 32, 20, 12, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 140)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound113 : QuotientRankAtLeast (spanCodes [260, 132, 66, 32, 18, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o196s8Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 142) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) 12 at h
  have hgen : ∀ c ∈ [260, 132, 66, 32, 18, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 142) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound114 : QuotientRankAtLeast (spanCodes [260, 132, 68, 34, 18, 10, 1]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (60 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 452))) 12 at h
  have hgen : ∀ c ∈ [260, 132, 68, 34, 18, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 452))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound115 : QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o76s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416 + QiushiMatmul.codeMat 84) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [260, 132, 68, 36, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416 + QiushiMatmul.codeMat 84) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound116 : QuotientRankAtLeast (spanCodes [260, 132, 69, 34, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (27 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) 15 at h
  have hgen : ∀ c ∈ [260, 132, 69, 34, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound117 : QuotientRankAtLeast (spanCodes [260, 132, 76, 32, 24, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o144s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264 + QiushiMatmul.codeMat 136 + QiushiMatmul.codeMat 28) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 28))) 12 at h
  have hgen : ∀ c ∈ [260, 132, 76, 32, 24, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264 + QiushiMatmul.codeMat 136 + QiushiMatmul.codeMat 28) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 28))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound118 : QuotientRankAtLeast (spanCodes [260, 132, 80, 48, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o217s5Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 148) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 14 at h
  have hgen : ∀ c ∈ [260, 132, 80, 48, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 148) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound119 : QuotientRankAtLeast (spanCodes [260, 133, 68, 36, 17, 8, 2]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (55 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 484))) 12 at h
  have hgen : ∀ c ∈ [260, 133, 68, 36, 17, 8, 2], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 484))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound120 : QuotientRankAtLeast (spanCodes [260, 133, 68, 38, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (28 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 478))) 15 at h
  have hgen : ∀ c ∈ [260, 133, 68, 38, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 478))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound121 : QuotientRankAtLeast (spanCodes [260, 134, 68, 38, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o65s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [260, 134, 68, 38, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound122 : QuotientRankAtLeast (spanCodes [260, 134, 96, 20, 14, 1]) 14 := by
  have h := QiushiMatmul.step99o237s10Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) 14 at h
  have hgen : ∀ c ∈ [260, 134, 96, 20, 14, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound123 : QuotientRankAtLeast (spanCodes [260, 135, 70, 38, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (29 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 250)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 286))) 15 at h
  have hgen : ∀ c ∈ [260, 135, 70, 38, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 250)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 286))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound124 : QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o65s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160))) 12 at h
  have hgen : ∀ c ∈ [260, 160, 68, 16, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 324) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound125 : QuotientRankAtLeast (spanCodes [260, 161, 68, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s1Dispatch
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 68) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [260, 161, 68, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 68) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound126 : QuotientRankAtLeast (spanCodes [260, 164, 68, 16, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o67s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 110) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160))) 12 at h
  have hgen : ∀ c ∈ [260, 164, 68, 16, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 110) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 160))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound127 : QuotientRankAtLeast (spanCodes [260, 164, 101, 19, 10]) 16 := by
  have h := QiushiMatmul.o435_dispatch_hSource (11 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) 16 at h
  have hgen : ∀ c ∈ [260, 164, 101, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound128 : QuotientRankAtLeast (spanCodes [261, 128, 65, 17, 8, 2]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (41 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 260))) 15 at h
  have hgen : ∀ c ∈ [261, 128, 65, 17, 8, 2], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 260))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound129 : QuotientRankAtLeast (spanCodes [261, 133, 68, 34, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (26 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) 15 at h
  have hgen : ∀ c ∈ [261, 133, 68, 34, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound130 : QuotientRankAtLeast (spanCodes [262, 128, 68, 32, 20, 10, 1]) 14 := by
  have h := QiushiMatmul.step81o17s4Pair_lb
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 340))) 14 at h
  have hgen : ∀ c ∈ [262, 128, 68, 32, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 340))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound131 : QuotientRankAtLeast (spanCodes [262, 130, 66, 34, 20, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o82s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [262, 130, 66, 34, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound132 : QuotientRankAtLeast (spanCodes [262, 130, 68, 38, 16, 10, 1]) 12 := by
  have h := QiushiMatmul.step99o68s5Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [262, 130, 68, 38, 16, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound133 : QuotientRankAtLeast (spanCodes [262, 132, 68, 37, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s9Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [262, 132, 68, 37, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound134 : QuotientRankAtLeast (spanCodes [262, 132, 96, 20, 12, 1]) 15 := by
  have h := QiushiMatmul.step99o237s1Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) 15 at h
  have hgen : ∀ c ∈ [262, 132, 96, 20, 12, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound135 : QuotientRankAtLeast (spanCodes [262, 133, 68, 36, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s8Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43))) 15 at h
  have hgen : ∀ c ∈ [262, 133, 68, 36, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound136 : QuotientRankAtLeast (spanCodes [262, 134, 68, 38, 20, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o76s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84 + QiushiMatmul.codeMat 10))) 14 at h
  have hgen : ∀ c ∈ [262, 134, 68, 38, 20, 10, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound137 : QuotientRankAtLeast (spanCodes [262, 134, 68, 39, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s7Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [262, 134, 68, 39, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound138 : QuotientRankAtLeast (spanCodes [262, 134, 71, 36, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (25 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) 15 at h
  have hgen : ∀ c ∈ [262, 134, 71, 36, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound139 : QuotientRankAtLeast (spanCodes [262, 135, 68, 38, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s6Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [262, 135, 68, 38, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound140 : QuotientRankAtLeast (spanCodes [262, 135, 70, 35, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (32 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 331))) 15 at h
  have hgen : ∀ c ∈ [262, 135, 70, 35, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 331))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound141 : QuotientRankAtLeast (spanCodes [262, 165, 100, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (3 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 222)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) 15 at h
  have hgen : ∀ c ∈ [262, 165, 100, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 222)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound142 : QuotientRankAtLeast (spanCodes [263, 128, 68, 33, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s12Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43))) 15 at h
  have hgen : ∀ c ∈ [263, 128, 68, 33, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound143 : QuotientRankAtLeast (spanCodes [263, 129, 68, 32, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s13Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [263, 129, 68, 32, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound144 : QuotientRankAtLeast (spanCodes [263, 130, 68, 35, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s10Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [263, 130, 68, 35, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 43 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound145 : QuotientRankAtLeast (spanCodes [263, 131, 68, 34, 19, 10]) 15 := by
  have h := QiushiMatmul.step99o377s11Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 68) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43))) 15 at h
  have hgen : ∀ c ∈ [263, 131, 68, 34, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 256 + QiushiMatmul.codeMat 68) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 43))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound146 : QuotientRankAtLeast (spanCodes [263, 134, 71, 35, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (33 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 452))) 15 at h
  have hgen : ∀ c ∈ [263, 134, 71, 35, 19, 10], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 452))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound147 : QuotientRankAtLeast (spanCodes [264, 136, 96, 20, 2, 1]) 14 := by
  have h := QiushiMatmul.step99o237s6Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 138) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) 14 at h
  have hgen : ∀ c ∈ [264, 136, 96, 20, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 138) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound148 : QuotientRankAtLeast (spanCodes [264, 140, 72, 32, 28, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o144s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264 + QiushiMatmul.codeMat 68) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 136 + QiushiMatmul.codeMat 28))) 12 at h
  have hgen : ∀ c ∈ [264, 140, 72, 32, 28, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264 + QiushiMatmul.codeMat 68) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 136 + QiushiMatmul.codeMat 28))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound149 : QuotientRankAtLeast (spanCodes [266, 136, 64, 32, 20, 1]) 14 := by
  have h := QiushiMatmul.step99o237s11Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) 14 at h
  have hgen : ∀ c ∈ [266, 136, 64, 32, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound150 : QuotientRankAtLeast (spanCodes [266, 136, 66, 34, 20, 1]) 15 := by
  have h := QiushiMatmul.step99o237s2Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 96) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) 15 at h
  have hgen : ∀ c ∈ [266, 136, 66, 34, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 96) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound151 : QuotientRankAtLeast (spanCodes [266, 136, 68, 36, 20, 1]) 14 := by
  have h := QiushiMatmul.step99o237s12Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) 14 at h
  have hgen : ∀ c ∈ [266, 136, 68, 36, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound152 : QuotientRankAtLeast (spanCodes [266, 136, 70, 38, 20, 1]) 15 := by
  have h := QiushiMatmul.step99o237s3Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) 15 at h
  have hgen : ∀ c ∈ [266, 136, 70, 38, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound153 : QuotientRankAtLeast (spanCodes [266, 136, 72, 40, 20, 1]) 14 := by
  have h := QiushiMatmul.step99o237s13Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) 14 at h
  have hgen : ∀ c ∈ [266, 136, 72, 40, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 96)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound154 : QuotientRankAtLeast (spanCodes [266, 136, 74, 42, 20, 1]) 14 := by
  have h := QiushiMatmul.step99o237s14Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 96) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) 14 at h
  have hgen : ∀ c ∈ [266, 136, 74, 42, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 96) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound155 : QuotientRankAtLeast (spanCodes [266, 136, 76, 44, 20, 1]) 15 := by
  have h := QiushiMatmul.step99o237s4Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) 15 at h
  have hgen : ∀ c ∈ [266, 136, 76, 44, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound156 : QuotientRankAtLeast (spanCodes [266, 136, 78, 46, 20, 1]) 15 := by
  have h := QiushiMatmul.step99o237s5Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) 15 at h
  have hgen : ∀ c ∈ [266, 136, 78, 46, 20, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96 + QiushiMatmul.codeMat 20))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound157 : QuotientRankAtLeast (spanCodes [266, 136, 96, 16, 4, 1]) 14 := by
  have h := QiushiMatmul.step99o237s7Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) 14 at h
  have hgen : ∀ c ∈ [266, 136, 96, 16, 4, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound158 : QuotientRankAtLeast (spanCodes [266, 136, 96, 18, 6, 1]) 14 := by
  have h := QiushiMatmul.step99o237s8Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) 14 at h
  have hgen : ∀ c ∈ [266, 136, 96, 18, 6, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 258 + QiushiMatmul.codeMat 20) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 138 + QiushiMatmul.codeMat 20)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 96))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound159 : QuotientRankAtLeast (spanCodes [268, 128, 64, 32, 20, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o144s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 28))) 12 at h
  have hgen : ∀ c ∈ [268, 128, 64, 32, 20, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 28))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound160 : QuotientRankAtLeast (spanCodes [272, 80, 32, 8, 4, 2, 1]) 9 := by
  have h := QiushiMatmul.step99o120s8Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128))) 9 at h
  have hgen : ∀ c ∈ [272, 80, 32, 8, 4, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound161 : QuotientRankAtLeast (spanCodes [272, 128, 32, 8, 4, 2, 1]) 9 := by
  have h := QiushiMatmul.step99o55s3Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) 9 at h
  have hgen : ∀ c ∈ [272, 128, 32, 8, 4, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound162 : QuotientRankAtLeast (spanCodes [272, 128, 64, 32, 8, 4, 2, 1]) 6 := by
  have h := QiushiMatmul.seed_ker_272
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272)) 6 at h
  have hgen : ∀ c ∈ [272, 128, 64, 32, 8, 4, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound163 : QuotientRankAtLeast (spanCodes [272, 128, 64, 32, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o120s6Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [272, 128, 64, 32, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound164 : QuotientRankAtLeast (spanCodes [272, 130, 32, 10, 6, 1]) 14 := by
  have h := QiushiMatmul.step99o196s2Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) 14 at h
  have hgen : ∀ c ∈ [272, 130, 32, 10, 6, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound165 : QuotientRankAtLeast (spanCodes [272, 130, 66, 34, 10, 6, 1]) 12 := by
  have h := QiushiMatmul.step99o217s7Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 112 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [272, 130, 66, 34, 10, 6, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 112 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound166 : QuotientRankAtLeast (spanCodes [272, 132, 32, 12, 2, 1]) 14 := by
  have h := QiushiMatmul.step99o120s0Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 12)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) 14 at h
  have hgen : ∀ c ∈ [272, 132, 32, 12, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 12)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound167 : QuotientRankAtLeast (spanCodes [272, 132, 68, 32, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o55s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140 + QiushiMatmul.codeMat 64))) 12 at h
  have hgen : ∀ c ∈ [272, 132, 68, 32, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140 + QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound168 : QuotientRankAtLeast (spanCodes [272, 132, 68, 36, 10, 1]) 15 := by
  have h := QiushiMatmul.step99o217s0Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 112)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 15 at h
  have hgen : ∀ c ∈ [272, 132, 68, 36, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 112)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound169 : QuotientRankAtLeast (spanCodes [272, 132, 80, 32, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o55s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140))) 12 at h
  have hgen : ∀ c ∈ [272, 132, 80, 32, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 140))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound170 : QuotientRankAtLeast (spanCodes [272, 144, 68, 32, 12, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o120s7Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 12))) 12 at h
  have hgen : ∀ c ∈ [272, 144, 68, 32, 12, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound171 : QuotientRankAtLeast (spanCodes [272, 148, 32, 12, 2, 1]) 14 := by
  have h := QiushiMatmul.step99o120s1Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 12)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) 14 at h
  have hgen : ∀ c ∈ [272, 148, 32, 12, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 12) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 12)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound172 : QuotientRankAtLeast (spanCodes [272, 196, 32, 12, 2, 1]) 14 := by
  have h := QiushiMatmul.step99o120s2Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 12)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 12))) 14 at h
  have hgen : ∀ c ∈ [272, 196, 32, 12, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 12)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound173 : QuotientRankAtLeast (spanCodes [272, 208, 32, 12, 2, 1]) 14 := by
  have h := QiushiMatmul.step99o120s3Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) 14 at h
  have hgen : ∀ c ∈ [272, 208, 32, 12, 2, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 12))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound174 : QuotientRankAtLeast (spanCodes [274, 132, 70, 38, 10, 1]) 15 := by
  have h := QiushiMatmul.step99o217s1Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 10)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112 + QiushiMatmul.codeMat 10))) 15 at h
  have hgen : ∀ c ∈ [274, 132, 70, 38, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 10)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound175 : QuotientRankAtLeast (spanCodes [276, 132, 64, 32, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o217s4Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 14 at h
  have hgen : ∀ c ∈ [276, 132, 64, 32, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound176 : QuotientRankAtLeast (spanCodes [276, 132, 80, 32, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o196s9Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142 + QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) 12 at h
  have hgen : ∀ c ∈ [276, 132, 80, 32, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142 + QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound177 : QuotientRankAtLeast (spanCodes [278, 132, 64, 32, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o196s4Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) 14 at h
  have hgen : ∀ c ∈ [278, 132, 64, 32, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound178 : QuotientRankAtLeast (spanCodes [278, 132, 68, 32, 10, 1]) 15 := by
  have h := QiushiMatmul.step99o196s0Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142 + QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [278, 132, 68, 32, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142 + QiushiMatmul.codeMat 64)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound179 : QuotientRankAtLeast (spanCodes [278, 132, 70, 32, 10, 1]) 15 := by
  have h := QiushiMatmul.step99o196s1Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) 15 at h
  have hgen : ∀ c ∈ [278, 132, 70, 32, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound180 : QuotientRankAtLeast (spanCodes [278, 132, 84, 32, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o196s5Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) 14 at h
  have hgen : ∀ c ∈ [278, 132, 84, 32, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142 + QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 64 + QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound181 : QuotientRankAtLeast (spanCodes [278, 132, 86, 32, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o196s6Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) 14 at h
  have hgen : ∀ c ∈ [278, 132, 86, 32, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 266 + QiushiMatmul.codeMat 64) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 142)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound182 : QuotientRankAtLeast (spanCodes [288, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s2Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11))) 17 at h
  have hgen : ∀ c ∈ [288, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound183 : QuotientRankAtLeast (spanCodes [288, 132, 96, 20, 10, 1]) 14 := by
  have h := QiushiMatmul.step99o217s3Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 112) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 14 at h
  have hgen : ∀ c ∈ [288, 132, 96, 20, 10, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 112) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound184 : QuotientRankAtLeast (spanCodes [288, 134, 71, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (12 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 288))) 15 at h
  have hgen : ∀ c ∈ [288, 134, 71, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 288))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound185 : QuotientRankAtLeast (spanCodes [288, 160, 64, 16, 8, 4, 2, 1]) 6 := by
  have h := QiushiMatmul.seed_ker_416
  change QuotientRankAtLeast (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416)) 6 at h
  have hgen : ∀ c ∈ [288, 160, 64, 16, 8, 4, 2, 1], codeMat c ∈ (QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416)) := by
    simp only [mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound186 : QuotientRankAtLeast (spanCodes [288, 160, 64, 16, 10, 4, 1]) 12 := by
  have h := QiushiMatmul.step99o76s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [288, 160, 64, 16, 10, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound187 : QuotientRankAtLeast (spanCodes [288, 160, 66, 18, 10, 6, 1]) 12 := by
  have h := QiushiMatmul.step99o76s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [288, 160, 66, 18, 10, 6, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 84 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound188 : QuotientRankAtLeast (spanCodes [288, 160, 96, 16, 10, 4, 1]) 9 := by
  have h := QiushiMatmul.step99o82s6Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 244) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 9 at h
  have hgen : ∀ c ∈ [288, 160, 96, 16, 10, 4, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 244) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound189 : QuotientRankAtLeast (spanCodes [288, 160, 97, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (6 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) 15 at h
  have hgen : ∀ c ∈ [288, 160, 97, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound190 : QuotientRankAtLeast (spanCodes [288, 161, 96, 16, 9, 4, 3]) 12 := by
  have h := QiushiMatmul.o435_dispatch_hSource (61 : Fin 63)
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 480))) 12 at h
  have hgen : ∀ c ∈ [288, 161, 96, 16, 9, 4, 3], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 480))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound191 : QuotientRankAtLeast (spanCodes [288, 161, 96, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (1 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 480))) 15 at h
  have hgen : ∀ c ∈ [288, 161, 96, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 4)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 480))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound192 : QuotientRankAtLeast (spanCodes [288, 162, 66, 16, 10, 6, 1]) 12 := by
  have h := QiushiMatmul.step99o68s2Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [288, 162, 66, 16, 10, 6, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound193 : QuotientRankAtLeast (spanCodes [288, 164, 68, 16, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o68s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196))) 12 at h
  have hgen : ∀ c ∈ [288, 164, 68, 16, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 356) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound194 : QuotientRankAtLeast (spanCodes [288, 164, 101, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (10 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) 15 at h
  have hgen : ∀ c ∈ [288, 164, 101, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound195 : QuotientRankAtLeast (spanCodes [288, 166, 103, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (13 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) 15 at h
  have hgen : ∀ c ∈ [288, 166, 103, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 433))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound196 : QuotientRankAtLeast (spanCodes [289, 132, 69, 19, 10]) 16 := by
  have h := QiushiMatmul.o435_dispatch_hSource (8 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) 16 at h
  have hgen : ∀ c ∈ [289, 132, 69, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 196)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound197 : QuotientRankAtLeast (spanCodes [290, 160, 96, 18, 10, 6, 1]) 12 := by
  have h := QiushiMatmul.step99o82s1Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244 + QiushiMatmul.codeMat 10))) 12 at h
  have hgen : ∀ c ∈ [290, 160, 96, 18, 10, 6, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276 + QiushiMatmul.codeMat 10) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244 + QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound198 : QuotientRankAtLeast (spanCodes [291, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s3Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 17))) 17 at h
  have hgen : ∀ c ∈ [291, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 17))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound199 : QuotientRankAtLeast (spanCodes [291, 160, 97, 19, 10, 7]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (40 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 286))) 15 at h
  have hgen : ∀ c ∈ [291, 160, 97, 19, 10, 7], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 181) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 286))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound200 : QuotientRankAtLeast (spanCodes [291, 161, 96, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (35 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 113)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) 15 at h
  have hgen : ∀ c ∈ [291, 161, 96, 19, 10, 4], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 113)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound201 : QuotientRankAtLeast (spanCodes [291, 162, 99, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (36 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 337))) 15 at h
  have hgen : ∀ c ∈ [291, 162, 99, 19, 10, 4], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 337))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound202 : QuotientRankAtLeast (spanCodes [291, 163, 98, 19, 10, 7]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (39 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) 15 at h
  have hgen : ∀ c ∈ [291, 163, 98, 19, 10, 7], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 62) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound203 : QuotientRankAtLeast (spanCodes [291, 167, 102, 19, 10]) 16 := by
  have h := QiushiMatmul.o435_dispatch_hSource (5 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) 16 at h
  have hgen : ∀ c ∈ [291, 167, 102, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound204 : QuotientRankAtLeast (spanCodes [292, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s4Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 68))) 17 at h
  have hgen : ∀ c ∈ [292, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 68))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound205 : QuotientRankAtLeast (spanCodes [292, 132, 96, 16, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o217s6Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 112) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 112))) 12 at h
  have hgen : ∀ c ∈ [292, 132, 96, 16, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272 + QiushiMatmul.codeMat 112) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 148 + QiushiMatmul.codeMat 112))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound206 : QuotientRankAtLeast (spanCodes [292, 133, 68, 19, 10]) 16 := by
  have h := QiushiMatmul.o435_dispatch_hSource (2 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 228)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 288))) 16 at h
  have hgen : ∀ c ∈ [292, 133, 68, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 26)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 228)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 288))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound207 : QuotientRankAtLeast (spanCodes [292, 160, 96, 20, 8, 2, 1]) 12 := by
  have h := QiushiMatmul.step99o82s0Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244))) 12 at h
  have hgen : ∀ c ∈ [292, 160, 96, 20, 8, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 276) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 244))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound208 : QuotientRankAtLeast (spanCodes [293, 129, 64, 16, 9, 3]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (42 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) 15 at h
  have hgen : ∀ c ∈ [293, 129, 64, 16, 9, 3], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound209 : QuotientRankAtLeast (spanCodes [294, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s5Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 11))) 17 at h
  have hgen : ∀ c ∈ [294, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32 + QiushiMatmul.codeMat 11))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound210 : QuotientRankAtLeast (spanCodes [295, 132, 69, 19, 10]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (9 : Fin 63)
  change QuotientRankAtLeast ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) 15 at h
  have hgen : ∀ c ∈ [295, 132, 69, 19, 10], codeMat c ∈ ((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 58)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound211 : QuotientRankAtLeast (spanCodes [304, 128, 96, 10, 4, 1]) 14 := by
  have h := QiushiMatmul.step99o217s2Dispatch
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) 14 at h
  have hgen : ∀ c ∈ [304, 128, 96, 10, 4, 1], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 112)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 10))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound212 : QuotientRankAtLeast (spanCodes [304, 160, 64, 8, 4, 2, 1]) 9 := by
  have h := QiushiMatmul.step81o8s2Pair_lb
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416))) 9 at h
  have hgen : ∀ c ∈ [304, 160, 64, 8, 4, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 272) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 416))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound213 : QuotientRankAtLeast (spanCodes [322, 193, 33, 19, 10, 6]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (48 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 222)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 286))) 15 at h
  have hgen : ∀ c ∈ [322, 193, 33, 19, 10, 6], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 222)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 286))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound214 : QuotientRankAtLeast (spanCodes [322, 193, 34, 19, 10, 6]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (47 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 254)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 318))) 15 at h
  have hgen : ∀ c ∈ [322, 193, 34, 19, 10, 6], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 145) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 254)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 318))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound215 : QuotientRankAtLeast (spanCodes [322, 193, 35, 19, 10, 4]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (46 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) 15 at h
  have hgen : ∀ c ∈ [322, 193, 35, 19, 10, 4], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 177) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 75)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 395))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound216 : QuotientRankAtLeast (spanCodes [323, 193, 32, 19, 10, 5]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (49 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) 15 at h
  have hgen : ∀ c ∈ [323, 193, 32, 19, 10, 5], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 218)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 282))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound217 : QuotientRankAtLeast (spanCodes [323, 193, 34, 19, 10, 7]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (53 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) 15 at h
  have hgen : ∀ c ∈ [323, 193, 34, 19, 10, 7], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 171) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 85)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 405))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound218 : QuotientRankAtLeast (spanCodes [323, 193, 35, 19, 10, 5]) 15 := by
  have h := QiushiMatmul.o435_dispatch_hSource (51 : Fin 63)
  change QuotientRankAtLeast (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 250)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 314))) 15 at h
  have hgen : ∀ c ∈ [323, 193, 35, 19, 10, 5], codeMat c ∈ (((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 143) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 250)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 314))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound219 : QuotientRankAtLeast (spanCodes [327, 193, 19, 10]) 16 := by
  have h := QiushiMatmul.o435_dispatch_hSource (0 : Fin 63)
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) 16 at h
  have hgen : ∀ c ∈ [327, 193, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 139) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 149)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 81)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 401))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound220 : QuotientRankAtLeast (spanCodes [384, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s6Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11))) 17 at h
  have hgen : ∀ c ∈ [384, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound221 : QuotientRankAtLeast (spanCodes [387, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s7Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 17))) 17 at h
  have hgen : ∀ c ∈ [387, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 17))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound222 : QuotientRankAtLeast (spanCodes [388, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s8Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68))) 17 at h
  have hgen : ∀ c ∈ [388, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 11)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound223 : QuotientRankAtLeast (spanCodes [390, 68, 19, 10]) 17 := by
  have h := QiushiMatmul.step108o450s9Dispatch
  change QuotientRankAtLeast (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 11))) 17 at h
  have hgen : ∀ c ∈ [390, 68, 19, 10], codeMat c ∈ (((((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 32) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 17)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 256)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 68)) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 128 + QiushiMatmul.codeMat 11))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

theorem bound224 : QuotientRankAtLeast (spanCodes [400, 80, 32, 8, 4, 2, 1]) 9 := by
  have h := QiushiMatmul.step99o144s4Dispatch
  change QuotientRankAtLeast ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 28) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 136 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 28))) 9 at h
  have hgen : ∀ c ∈ [400, 80, 32, 8, 4, 2, 1], codeMat c ∈ ((QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 264 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 28) ⊓ QiushiMatmul.kerEvalFunc (QiushiMatmul.codeMat 136 + QiushiMatmul.codeMat 68 + QiushiMatmul.codeMat 28))) := by
    simp only [Submodule.mem_inf, mem_kerEvalFunc]
    decide
  apply quotientRankAtLeast_mono ?_ h
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact hgen c hc

end QiushiMatmul.FrozenRegistry.Kernel

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``QiushiMatmul.FrozenRegistry.Kernel.bound000, ``QiushiMatmul.FrozenRegistry.Kernel.bound001, ``QiushiMatmul.FrozenRegistry.Kernel.bound002, ``QiushiMatmul.FrozenRegistry.Kernel.bound003, ``QiushiMatmul.FrozenRegistry.Kernel.bound004, ``QiushiMatmul.FrozenRegistry.Kernel.bound005, ``QiushiMatmul.FrozenRegistry.Kernel.bound006, ``QiushiMatmul.FrozenRegistry.Kernel.bound007, ``QiushiMatmul.FrozenRegistry.Kernel.bound008, ``QiushiMatmul.FrozenRegistry.Kernel.bound009, ``QiushiMatmul.FrozenRegistry.Kernel.bound010, ``QiushiMatmul.FrozenRegistry.Kernel.bound011, ``QiushiMatmul.FrozenRegistry.Kernel.bound012, ``QiushiMatmul.FrozenRegistry.Kernel.bound013, ``QiushiMatmul.FrozenRegistry.Kernel.bound014, ``QiushiMatmul.FrozenRegistry.Kernel.bound015, ``QiushiMatmul.FrozenRegistry.Kernel.bound016, ``QiushiMatmul.FrozenRegistry.Kernel.bound017, ``QiushiMatmul.FrozenRegistry.Kernel.bound018, ``QiushiMatmul.FrozenRegistry.Kernel.bound019, ``QiushiMatmul.FrozenRegistry.Kernel.bound020, ``QiushiMatmul.FrozenRegistry.Kernel.bound021, ``QiushiMatmul.FrozenRegistry.Kernel.bound022, ``QiushiMatmul.FrozenRegistry.Kernel.bound023, ``QiushiMatmul.FrozenRegistry.Kernel.bound024, ``QiushiMatmul.FrozenRegistry.Kernel.bound025, ``QiushiMatmul.FrozenRegistry.Kernel.bound026, ``QiushiMatmul.FrozenRegistry.Kernel.bound027, ``QiushiMatmul.FrozenRegistry.Kernel.bound028, ``QiushiMatmul.FrozenRegistry.Kernel.bound029, ``QiushiMatmul.FrozenRegistry.Kernel.bound030, ``QiushiMatmul.FrozenRegistry.Kernel.bound031, ``QiushiMatmul.FrozenRegistry.Kernel.bound032, ``QiushiMatmul.FrozenRegistry.Kernel.bound033, ``QiushiMatmul.FrozenRegistry.Kernel.bound034, ``QiushiMatmul.FrozenRegistry.Kernel.bound035, ``QiushiMatmul.FrozenRegistry.Kernel.bound036, ``QiushiMatmul.FrozenRegistry.Kernel.bound037, ``QiushiMatmul.FrozenRegistry.Kernel.bound038, ``QiushiMatmul.FrozenRegistry.Kernel.bound039, ``QiushiMatmul.FrozenRegistry.Kernel.bound040, ``QiushiMatmul.FrozenRegistry.Kernel.bound041, ``QiushiMatmul.FrozenRegistry.Kernel.bound042, ``QiushiMatmul.FrozenRegistry.Kernel.bound043, ``QiushiMatmul.FrozenRegistry.Kernel.bound044, ``QiushiMatmul.FrozenRegistry.Kernel.bound045, ``QiushiMatmul.FrozenRegistry.Kernel.bound046, ``QiushiMatmul.FrozenRegistry.Kernel.bound047, ``QiushiMatmul.FrozenRegistry.Kernel.bound048, ``QiushiMatmul.FrozenRegistry.Kernel.bound049, ``QiushiMatmul.FrozenRegistry.Kernel.bound050, ``QiushiMatmul.FrozenRegistry.Kernel.bound051, ``QiushiMatmul.FrozenRegistry.Kernel.bound052, ``QiushiMatmul.FrozenRegistry.Kernel.bound053, ``QiushiMatmul.FrozenRegistry.Kernel.bound054, ``QiushiMatmul.FrozenRegistry.Kernel.bound055, ``QiushiMatmul.FrozenRegistry.Kernel.bound056, ``QiushiMatmul.FrozenRegistry.Kernel.bound057, ``QiushiMatmul.FrozenRegistry.Kernel.bound058, ``QiushiMatmul.FrozenRegistry.Kernel.bound059, ``QiushiMatmul.FrozenRegistry.Kernel.bound060, ``QiushiMatmul.FrozenRegistry.Kernel.bound061, ``QiushiMatmul.FrozenRegistry.Kernel.bound062, ``QiushiMatmul.FrozenRegistry.Kernel.bound063, ``QiushiMatmul.FrozenRegistry.Kernel.bound064, ``QiushiMatmul.FrozenRegistry.Kernel.bound065, ``QiushiMatmul.FrozenRegistry.Kernel.bound066, ``QiushiMatmul.FrozenRegistry.Kernel.bound067, ``QiushiMatmul.FrozenRegistry.Kernel.bound068, ``QiushiMatmul.FrozenRegistry.Kernel.bound069, ``QiushiMatmul.FrozenRegistry.Kernel.bound070, ``QiushiMatmul.FrozenRegistry.Kernel.bound071, ``QiushiMatmul.FrozenRegistry.Kernel.bound072, ``QiushiMatmul.FrozenRegistry.Kernel.bound073, ``QiushiMatmul.FrozenRegistry.Kernel.bound074, ``QiushiMatmul.FrozenRegistry.Kernel.bound075, ``QiushiMatmul.FrozenRegistry.Kernel.bound076, ``QiushiMatmul.FrozenRegistry.Kernel.bound077, ``QiushiMatmul.FrozenRegistry.Kernel.bound078, ``QiushiMatmul.FrozenRegistry.Kernel.bound079, ``QiushiMatmul.FrozenRegistry.Kernel.bound080, ``QiushiMatmul.FrozenRegistry.Kernel.bound081, ``QiushiMatmul.FrozenRegistry.Kernel.bound082, ``QiushiMatmul.FrozenRegistry.Kernel.bound083, ``QiushiMatmul.FrozenRegistry.Kernel.bound084, ``QiushiMatmul.FrozenRegistry.Kernel.bound085, ``QiushiMatmul.FrozenRegistry.Kernel.bound086, ``QiushiMatmul.FrozenRegistry.Kernel.bound087, ``QiushiMatmul.FrozenRegistry.Kernel.bound088, ``QiushiMatmul.FrozenRegistry.Kernel.bound089, ``QiushiMatmul.FrozenRegistry.Kernel.bound090, ``QiushiMatmul.FrozenRegistry.Kernel.bound091, ``QiushiMatmul.FrozenRegistry.Kernel.bound092, ``QiushiMatmul.FrozenRegistry.Kernel.bound093, ``QiushiMatmul.FrozenRegistry.Kernel.bound094, ``QiushiMatmul.FrozenRegistry.Kernel.bound095, ``QiushiMatmul.FrozenRegistry.Kernel.bound096, ``QiushiMatmul.FrozenRegistry.Kernel.bound097, ``QiushiMatmul.FrozenRegistry.Kernel.bound098, ``QiushiMatmul.FrozenRegistry.Kernel.bound099, ``QiushiMatmul.FrozenRegistry.Kernel.bound100, ``QiushiMatmul.FrozenRegistry.Kernel.bound101, ``QiushiMatmul.FrozenRegistry.Kernel.bound102, ``QiushiMatmul.FrozenRegistry.Kernel.bound103, ``QiushiMatmul.FrozenRegistry.Kernel.bound104, ``QiushiMatmul.FrozenRegistry.Kernel.bound105, ``QiushiMatmul.FrozenRegistry.Kernel.bound106, ``QiushiMatmul.FrozenRegistry.Kernel.bound107, ``QiushiMatmul.FrozenRegistry.Kernel.bound108, ``QiushiMatmul.FrozenRegistry.Kernel.bound109, ``QiushiMatmul.FrozenRegistry.Kernel.bound110, ``QiushiMatmul.FrozenRegistry.Kernel.bound111, ``QiushiMatmul.FrozenRegistry.Kernel.bound112, ``QiushiMatmul.FrozenRegistry.Kernel.bound113, ``QiushiMatmul.FrozenRegistry.Kernel.bound114, ``QiushiMatmul.FrozenRegistry.Kernel.bound115, ``QiushiMatmul.FrozenRegistry.Kernel.bound116, ``QiushiMatmul.FrozenRegistry.Kernel.bound117, ``QiushiMatmul.FrozenRegistry.Kernel.bound118, ``QiushiMatmul.FrozenRegistry.Kernel.bound119, ``QiushiMatmul.FrozenRegistry.Kernel.bound120, ``QiushiMatmul.FrozenRegistry.Kernel.bound121, ``QiushiMatmul.FrozenRegistry.Kernel.bound122, ``QiushiMatmul.FrozenRegistry.Kernel.bound123, ``QiushiMatmul.FrozenRegistry.Kernel.bound124, ``QiushiMatmul.FrozenRegistry.Kernel.bound125, ``QiushiMatmul.FrozenRegistry.Kernel.bound126, ``QiushiMatmul.FrozenRegistry.Kernel.bound127, ``QiushiMatmul.FrozenRegistry.Kernel.bound128, ``QiushiMatmul.FrozenRegistry.Kernel.bound129, ``QiushiMatmul.FrozenRegistry.Kernel.bound130, ``QiushiMatmul.FrozenRegistry.Kernel.bound131, ``QiushiMatmul.FrozenRegistry.Kernel.bound132, ``QiushiMatmul.FrozenRegistry.Kernel.bound133, ``QiushiMatmul.FrozenRegistry.Kernel.bound134, ``QiushiMatmul.FrozenRegistry.Kernel.bound135, ``QiushiMatmul.FrozenRegistry.Kernel.bound136, ``QiushiMatmul.FrozenRegistry.Kernel.bound137, ``QiushiMatmul.FrozenRegistry.Kernel.bound138, ``QiushiMatmul.FrozenRegistry.Kernel.bound139, ``QiushiMatmul.FrozenRegistry.Kernel.bound140, ``QiushiMatmul.FrozenRegistry.Kernel.bound141, ``QiushiMatmul.FrozenRegistry.Kernel.bound142, ``QiushiMatmul.FrozenRegistry.Kernel.bound143, ``QiushiMatmul.FrozenRegistry.Kernel.bound144, ``QiushiMatmul.FrozenRegistry.Kernel.bound145, ``QiushiMatmul.FrozenRegistry.Kernel.bound146, ``QiushiMatmul.FrozenRegistry.Kernel.bound147, ``QiushiMatmul.FrozenRegistry.Kernel.bound148, ``QiushiMatmul.FrozenRegistry.Kernel.bound149, ``QiushiMatmul.FrozenRegistry.Kernel.bound150, ``QiushiMatmul.FrozenRegistry.Kernel.bound151, ``QiushiMatmul.FrozenRegistry.Kernel.bound152, ``QiushiMatmul.FrozenRegistry.Kernel.bound153, ``QiushiMatmul.FrozenRegistry.Kernel.bound154, ``QiushiMatmul.FrozenRegistry.Kernel.bound155, ``QiushiMatmul.FrozenRegistry.Kernel.bound156, ``QiushiMatmul.FrozenRegistry.Kernel.bound157, ``QiushiMatmul.FrozenRegistry.Kernel.bound158, ``QiushiMatmul.FrozenRegistry.Kernel.bound159, ``QiushiMatmul.FrozenRegistry.Kernel.bound160, ``QiushiMatmul.FrozenRegistry.Kernel.bound161, ``QiushiMatmul.FrozenRegistry.Kernel.bound162, ``QiushiMatmul.FrozenRegistry.Kernel.bound163, ``QiushiMatmul.FrozenRegistry.Kernel.bound164, ``QiushiMatmul.FrozenRegistry.Kernel.bound165, ``QiushiMatmul.FrozenRegistry.Kernel.bound166, ``QiushiMatmul.FrozenRegistry.Kernel.bound167, ``QiushiMatmul.FrozenRegistry.Kernel.bound168, ``QiushiMatmul.FrozenRegistry.Kernel.bound169, ``QiushiMatmul.FrozenRegistry.Kernel.bound170, ``QiushiMatmul.FrozenRegistry.Kernel.bound171, ``QiushiMatmul.FrozenRegistry.Kernel.bound172, ``QiushiMatmul.FrozenRegistry.Kernel.bound173, ``QiushiMatmul.FrozenRegistry.Kernel.bound174, ``QiushiMatmul.FrozenRegistry.Kernel.bound175, ``QiushiMatmul.FrozenRegistry.Kernel.bound176, ``QiushiMatmul.FrozenRegistry.Kernel.bound177, ``QiushiMatmul.FrozenRegistry.Kernel.bound178, ``QiushiMatmul.FrozenRegistry.Kernel.bound179, ``QiushiMatmul.FrozenRegistry.Kernel.bound180, ``QiushiMatmul.FrozenRegistry.Kernel.bound181, ``QiushiMatmul.FrozenRegistry.Kernel.bound182, ``QiushiMatmul.FrozenRegistry.Kernel.bound183, ``QiushiMatmul.FrozenRegistry.Kernel.bound184, ``QiushiMatmul.FrozenRegistry.Kernel.bound185, ``QiushiMatmul.FrozenRegistry.Kernel.bound186, ``QiushiMatmul.FrozenRegistry.Kernel.bound187, ``QiushiMatmul.FrozenRegistry.Kernel.bound188, ``QiushiMatmul.FrozenRegistry.Kernel.bound189, ``QiushiMatmul.FrozenRegistry.Kernel.bound190, ``QiushiMatmul.FrozenRegistry.Kernel.bound191, ``QiushiMatmul.FrozenRegistry.Kernel.bound192, ``QiushiMatmul.FrozenRegistry.Kernel.bound193, ``QiushiMatmul.FrozenRegistry.Kernel.bound194, ``QiushiMatmul.FrozenRegistry.Kernel.bound195, ``QiushiMatmul.FrozenRegistry.Kernel.bound196, ``QiushiMatmul.FrozenRegistry.Kernel.bound197, ``QiushiMatmul.FrozenRegistry.Kernel.bound198, ``QiushiMatmul.FrozenRegistry.Kernel.bound199, ``QiushiMatmul.FrozenRegistry.Kernel.bound200, ``QiushiMatmul.FrozenRegistry.Kernel.bound201, ``QiushiMatmul.FrozenRegistry.Kernel.bound202, ``QiushiMatmul.FrozenRegistry.Kernel.bound203, ``QiushiMatmul.FrozenRegistry.Kernel.bound204, ``QiushiMatmul.FrozenRegistry.Kernel.bound205, ``QiushiMatmul.FrozenRegistry.Kernel.bound206, ``QiushiMatmul.FrozenRegistry.Kernel.bound207, ``QiushiMatmul.FrozenRegistry.Kernel.bound208, ``QiushiMatmul.FrozenRegistry.Kernel.bound209, ``QiushiMatmul.FrozenRegistry.Kernel.bound210, ``QiushiMatmul.FrozenRegistry.Kernel.bound211, ``QiushiMatmul.FrozenRegistry.Kernel.bound212, ``QiushiMatmul.FrozenRegistry.Kernel.bound213, ``QiushiMatmul.FrozenRegistry.Kernel.bound214, ``QiushiMatmul.FrozenRegistry.Kernel.bound215, ``QiushiMatmul.FrozenRegistry.Kernel.bound216, ``QiushiMatmul.FrozenRegistry.Kernel.bound217, ``QiushiMatmul.FrozenRegistry.Kernel.bound218, ``QiushiMatmul.FrozenRegistry.Kernel.bound219, ``QiushiMatmul.FrozenRegistry.Kernel.bound220, ``QiushiMatmul.FrozenRegistry.Kernel.bound221, ``QiushiMatmul.FrozenRegistry.Kernel.bound222, ``QiushiMatmul.FrozenRegistry.Kernel.bound223, ``QiushiMatmul.FrozenRegistry.Kernel.bound224] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"KERNEL_BOUND_AXIOMS {name}: {axioms}"
  Lean.logInfo "KERNEL_BOUND_CHECKED 225"
