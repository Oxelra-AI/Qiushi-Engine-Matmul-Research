import FrozenRegistry.Bridge
import FrozenRegistry.UnusedAdapters
import FrozenRegistry.Seed020
import FrozenRegistry.ClosedReductions
import FrozenRegistry.Btp420Final
import FrozenRegistry.Btp410Final
import FrozenRegistry.Btp287Final
import FrozenRegistry.Btp285Final
import FrozenRegistry.Btp265Final
import FrozenRegistry.Btp263Final
import FrozenRegistry.Btp261Final
import FrozenRegistry.Btp227Final
import FrozenRegistry.Btp224Final
import FrozenRegistry.TransportBindings

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace QiushiMatmul.FrozenRegistry

theorem rep000 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 0))
      (frozenWangTable.lower 0) := by
  rw [show frozenWangTable.basis 0 = [256, 128, 64, 32, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 0 = 0 by decide]
  intro r hr
  omega

theorem rep001 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 1))
      (frozenWangTable.lower 1) := by
  rw [show frozenWangTable.basis 1 = [128, 64, 32, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 1 = 3 by decide]
  have h := QiushiMatmul.flatSeed_1
  change QuotientRankAtLeast (spanCodes [128, 64, 32, 16, 8, 4, 2, 1]) 3 at h
  exact bind_exact
    [128, 64, 32, 16, 8, 4, 2, 1] [128, 64, 32, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep002 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 2))
      (frozenWangTable.lower 2) := by
  rw [show frozenWangTable.basis 2 = [256, 160, 64, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 2 = 6 by decide]
  have h := QiushiMatmul.flatSeed_2
  change QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 8, 4, 2, 1]) 6 at h
  exact bind_exact
    [256, 160, 64, 16, 8, 4, 2, 1] [256, 160, 64, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep003 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 3))
      (frozenWangTable.lower 3) := by
  rw [show frozenWangTable.basis 3 = [256, 128, 68, 32, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 3 = 9 by decide]
  have h := QiushiMatmul.flatSeed_3
  change QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 at h
  exact bind_exact
    [256, 128, 68, 32, 20, 8, 2, 1] [256, 128, 68, 32, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep004 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 4))
      (frozenWangTable.lower 4) := by
  rw [show frozenWangTable.basis 4 = [64, 32, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 4 = 6 by decide]
  have h := QiushiMatmul.flatSeed_4
  change QuotientRankAtLeast (spanCodes [64, 32, 16, 8, 4, 2, 1]) 6 at h
  exact bind_exact
    [64, 32, 16, 8, 4, 2, 1] [64, 32, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep005 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 5))
      (frozenWangTable.lower 5) := by
  rw [show frozenWangTable.basis 5 = [160, 64, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 5 = 9 by decide]
  have h := QiushiMatmul.orbit5_lb9
  change QuotientRankAtLeast (spanCodes [1, 2, 4, 8, 16, 64, 160]) 9 at h
  exact bind_exact
    [160, 64, 16, 8, 4, 2, 1] [1, 2, 4, 8, 16, 64, 160] h
    (by decide) (by decide) (by decide)

theorem rep006 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 6))
      (frozenWangTable.lower 6) := by
  rw [show frozenWangTable.basis 6 = [256, 64, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 6 = 6 by decide]
  have h := QiushiMatmul.flatSeed_6
  change QuotientRankAtLeast (spanCodes [256, 64, 16, 8, 4, 2, 1]) 6 at h
  exact bind_exact
    [256, 64, 16, 8, 4, 2, 1] [256, 64, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep007 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 7))
      (frozenWangTable.lower 7) := by
  rw [show frozenWangTable.basis 7 = [256, 96, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 7 = 9 by decide]
  have h := QiushiMatmul.flatSeed_7
  change QuotientRankAtLeast (spanCodes [256, 96, 16, 8, 4, 2, 1]) 9 at h
  exact bind_exact
    [256, 96, 16, 8, 4, 2, 1] [256, 96, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep008 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 8))
      (frozenWangTable.lower 8) := by
  rw [show frozenWangTable.basis 8 = [304, 160, 64, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 8 = 9 by decide]
  have h := QiushiMatmul.orbit8_lb9
  change QuotientRankAtLeast (spanCodes [304, 160, 64, 8, 4, 2, 1]) 9 at h
  exact bind_exact
    [304, 160, 64, 8, 4, 2, 1] [304, 160, 64, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep009 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 9))
      (frozenWangTable.lower 9) := by
  rw [show frozenWangTable.basis 9 = [256, 160, 80, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 9 = 9 by decide]
  have h := QiushiMatmul.flatSeed_9
  change QuotientRankAtLeast (spanCodes [256, 160, 80, 8, 4, 2, 1]) 9 at h
  exact bind_exact
    [256, 160, 80, 8, 4, 2, 1] [256, 160, 80, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep010 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 10))
      (frozenWangTable.lower 10) := by
  rw [show frozenWangTable.basis 10 = [256, 160, 68, 16, 8, 2, 1] by decide,
      show frozenWangTable.lower 10 = 12 by decide]
  have h := QiushiMatmul.orbit10_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 16, 68, 160, 256]) 12 at h
  exact bind_exact
    [256, 160, 68, 16, 8, 2, 1] [1, 2, 8, 16, 68, 160, 256] h
    (by decide) (by decide) (by decide)

theorem rep011 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 11))
      (frozenWangTable.lower 11) := by
  rw [show frozenWangTable.basis 11 = [128, 68, 32, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 11 = 12 by decide]
  have h := QiushiMatmul.orbit11_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 20, 32, 68, 128]) 12 at h
  exact bind_exact
    [128, 68, 32, 20, 8, 2, 1] [1, 2, 8, 20, 32, 68, 128] h
    (by decide) (by decide) (by decide)

theorem rep012 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 12))
      (frozenWangTable.lower 12) := by
  rw [show frozenWangTable.basis 12 = [256, 128, 32, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 12 = 9 by decide]
  have h := QiushiMatmul.flatSeed_12
  change QuotientRankAtLeast (spanCodes [256, 128, 32, 20, 8, 2, 1]) 9 at h
  exact bind_exact
    [256, 128, 32, 20, 8, 2, 1] [256, 128, 32, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep013 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 13))
      (frozenWangTable.lower 13) := by
  rw [show frozenWangTable.basis 13 = [256, 160, 68, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 13 = 12 by decide]
  have h := QiushiMatmul.orbit13_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 20, 68, 160, 256]) 12 at h
  exact bind_exact
    [256, 160, 68, 20, 8, 2, 1] [1, 2, 8, 20, 68, 160, 256] h
    (by decide) (by decide) (by decide)

theorem rep014 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 14))
      (frozenWangTable.lower 14) := by
  rw [show frozenWangTable.basis 14 = [256, 128, 96, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 14 = 12 by decide]
  have h := QiushiMatmul.orbit14_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 20, 96, 128, 256]) 12 at h
  exact bind_exact
    [256, 128, 96, 20, 8, 2, 1] [1, 2, 8, 20, 96, 128, 256] h
    (by decide) (by decide) (by decide)

theorem rep015 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 15))
      (frozenWangTable.lower 15) := by
  rw [show frozenWangTable.basis 15 = [256, 128, 84, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 15 = 9 by decide]
  have h := QiushiMatmul.flatSeed_15
  change QuotientRankAtLeast (spanCodes [256, 128, 84, 32, 8, 2, 1]) 9 at h
  exact bind_exact
    [256, 128, 84, 32, 8, 2, 1] [256, 128, 84, 32, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep016 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 16))
      (frozenWangTable.lower 16) := by
  rw [show frozenWangTable.basis 16 = [256, 148, 80, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 16 = 12 by decide]
  have h := QiushiMatmul.step81o16s2Span_lb
  change QuotientRankAtLeast (spanCodes [256, 148, 80, 32, 12, 2, 1]) 12 at h
  exact bind_exact
    [256, 148, 80, 32, 12, 2, 1] [256, 148, 80, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep017 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 17))
      (frozenWangTable.lower 17) := by
  rw [show frozenWangTable.basis 17 = [262, 128, 68, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 17 = 14 by decide]
  have h := QiushiMatmul.step81o17s4Span_lb
  change QuotientRankAtLeast (spanCodes [262, 128, 68, 32, 20, 10, 1]) 14 at h
  exact bind_exact
    [262, 128, 68, 32, 20, 10, 1] [262, 128, 68, 32, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep018 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 18))
      (frozenWangTable.lower 18) := by
  rw [show frozenWangTable.basis 18 = [32, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 18 = 9 by decide]
  have h := QiushiMatmul.flatSeed_18
  change QuotientRankAtLeast (spanCodes [32, 16, 8, 4, 2, 1]) 9 at h
  exact bind_exact
    [32, 16, 8, 4, 2, 1] [32, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep019 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 19))
      (frozenWangTable.lower 19) := by
  rw [show frozenWangTable.basis 19 = [64, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 19 = 9 by decide]
  have h := QiushiMatmul.orbit19_lb9_mono
  change QuotientRankAtLeast (spanCodes [64, 16, 8, 4, 2, 1]) 9 at h
  exact bind_exact
    [64, 16, 8, 4, 2, 1] [64, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep020 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 20))
      (frozenWangTable.lower 20) := by
  rw [show frozenWangTable.basis 20 = [96, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 20 = 12 by decide]
  have h := QiushiMatmul.FrozenRegistry.Seed020.qra12
  change QuotientRankAtLeast (spanCodes [96, 16, 8, 4, 2, 1]) 12 at h
  exact bind_exact
    [96, 16, 8, 4, 2, 1] [96, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep021 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 21))
      (frozenWangTable.lower 21) := by
  rw [show frozenWangTable.basis 21 = [256, 16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 21 = 9 by decide]
  have h := QiushiMatmul.flatSeed_21
  change QuotientRankAtLeast (spanCodes [256, 16, 8, 4, 2, 1]) 9 at h
  exact bind_exact
    [256, 16, 8, 4, 2, 1] [256, 16, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep022 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 22))
      (frozenWangTable.lower 22) := by
  rw [show frozenWangTable.basis 22 = [160, 64, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 22 = 9 by decide]
  have h := QiushiMatmul.orbit5_lb9
  change QuotientRankAtLeast (spanCodes [1, 2, 4, 8, 16, 64, 160]) 9 at h
  exact bind_contained
    [160, 64, 8, 4, 2, 1] [1, 2, 4, 8, 16, 64, 160] h
    (by decide) (by decide)

theorem rep023 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 23))
      (frozenWangTable.lower 23) := by
  rw [show frozenWangTable.basis 23 = [128, 80, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 23 = 12 by decide]
  have h := QiushiMatmul.orbit23_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 4, 8, 80, 128]) 12 at h
  exact bind_exact
    [128, 80, 8, 4, 2, 1] [1, 2, 4, 8, 80, 128] h
    (by decide) (by decide) (by decide)

theorem rep024 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 24))
      (frozenWangTable.lower 24) := by
  rw [show frozenWangTable.basis 24 = [160, 80, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 24 = 11 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound024
  change QuotientRankAtLeast (spanCodes [160, 80, 8, 4, 2, 1]) 11 at h
  exact bind_exact
    [160, 80, 8, 4, 2, 1] [160, 80, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep025 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 25))
      (frozenWangTable.lower 25) := by
  rw [show frozenWangTable.basis 25 = [256, 80, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 25 = 12 by decide]
  have h := QiushiMatmul.orbit25_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 4, 8, 80, 256]) 12 at h
  exact bind_exact
    [256, 80, 8, 4, 2, 1] [1, 2, 4, 8, 80, 256] h
    (by decide) (by decide) (by decide)

theorem rep026 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 26))
      (frozenWangTable.lower 26) := by
  rw [show frozenWangTable.basis 26 = [288, 128, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 26 = 9 by decide]
  have h := QiushiMatmul.flatSeed_26
  change QuotientRankAtLeast (spanCodes [288, 128, 8, 4, 2, 1]) 9 at h
  exact bind_exact
    [288, 128, 8, 4, 2, 1] [288, 128, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep027 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 27))
      (frozenWangTable.lower 27) := by
  rw [show frozenWangTable.basis 27 = [304, 160, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 27 = 11 by decide]
  have h := QiushiMatmul.FrozenRank.span027_lb11
  change QuotientRankAtLeast (spanCodes [304, 160, 8, 4, 2, 1]) 11 at h
  exact bind_exact
    [304, 160, 8, 4, 2, 1] [304, 160, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep028 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 28))
      (frozenWangTable.lower 28) := by
  rw [show frozenWangTable.basis 28 = [280, 160, 80, 4, 2, 1] by decide,
      show frozenWangTable.lower 28 = 11 by decide]
  have h := QiushiMatmul.FrozenRank.span028_lb11
  change QuotientRankAtLeast (spanCodes [280, 160, 80, 4, 2, 1]) 11 at h
  exact bind_exact
    [280, 160, 80, 4, 2, 1] [280, 160, 80, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep029 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 29))
      (frozenWangTable.lower 29) := by
  rw [show frozenWangTable.basis 29 = [160, 68, 16, 8, 2, 1] by decide,
      show frozenWangTable.lower 29 = 15 by decide]
  have h := QiushiMatmul.orbit29_lb15
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 16, 68, 160]) 15 at h
  exact bind_exact
    [160, 68, 16, 8, 2, 1] [1, 2, 8, 16, 68, 160] h
    (by decide) (by decide) (by decide)

theorem rep030 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 30))
      (frozenWangTable.lower 30) := by
  rw [show frozenWangTable.basis 30 = [256, 68, 16, 8, 2, 1] by decide,
      show frozenWangTable.lower 30 = 12 by decide]
  have h := QiushiMatmul.step99_mono_30_lb12
  change QuotientRankAtLeast (spanCodes [256, 68, 16, 8, 2, 1]) 12 at h
  exact bind_exact
    [256, 68, 16, 8, 2, 1] [256, 68, 16, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep031 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 31))
      (frozenWangTable.lower 31) := by
  rw [show frozenWangTable.basis 31 = [68, 32, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 31 = 15 by decide]
  have h := QiushiMatmul.orbit31_lb15
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 20, 32, 68]) 15 at h
  exact bind_exact
    [68, 32, 20, 8, 2, 1] [1, 2, 8, 20, 32, 68] h
    (by decide) (by decide) (by decide)

theorem rep032 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 32))
      (frozenWangTable.lower 32) := by
  rw [show frozenWangTable.basis 32 = [128, 32, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 32 = 12 by decide]
  have h := QiushiMatmul.step99_mono_32_lb12
  change QuotientRankAtLeast (spanCodes [128, 32, 20, 8, 2, 1]) 12 at h
  exact bind_exact
    [128, 32, 20, 8, 2, 1] [128, 32, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep033 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 33))
      (frozenWangTable.lower 33) := by
  rw [show frozenWangTable.basis 33 = [160, 68, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 33 = 14 by decide]
  have h := QiushiMatmul.FrozenRank.span033_lb14
  change QuotientRankAtLeast (spanCodes [160, 68, 20, 8, 2, 1]) 14 at h
  exact bind_exact
    [160, 68, 20, 8, 2, 1] [160, 68, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep034 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 34))
      (frozenWangTable.lower 34) := by
  rw [show frozenWangTable.basis 34 = [256, 68, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 34 = 14 by decide]
  have h := QiushiMatmul.step99_orbit34_lb14_unconditional
  change QuotientRankAtLeast (spanCodes [256, 68, 20, 8, 2, 1]) 14 at h
  exact bind_exact
    [256, 68, 20, 8, 2, 1] [256, 68, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep035 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 35))
      (frozenWangTable.lower 35) := by
  rw [show frozenWangTable.basis 35 = [128, 96, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 35 = 15 by decide]
  have h := QiushiMatmul.orbit35_lb15
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 20, 96, 128]) 15 at h
  exact bind_exact
    [128, 96, 20, 8, 2, 1] [1, 2, 8, 20, 96, 128] h
    (by decide) (by decide) (by decide)

theorem rep036 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 36))
      (frozenWangTable.lower 36) := by
  rw [show frozenWangTable.basis 36 = [256, 96, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 36 = 13 by decide]
  have h := QiushiMatmul.step109wc164s9Dispatch
  change QuotientRankAtLeast (spanCodes [256, 96, 20, 8, 2, 1]) 13 at h
  exact bind_exact
    [256, 96, 20, 8, 2, 1] [256, 96, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep037 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 37))
      (frozenWangTable.lower 37) := by
  rw [show frozenWangTable.basis 37 = [256, 128, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 37 = 12 by decide]
  have h := QiushiMatmul.orbit14_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 20, 96, 128, 256]) 12 at h
  exact bind_contained
    [256, 128, 20, 8, 2, 1] [1, 2, 8, 20, 96, 128, 256] h
    (by decide) (by decide)

theorem rep038 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 38))
      (frozenWangTable.lower 38) := by
  rw [show frozenWangTable.basis 38 = [288, 128, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 38 = 12 by decide]
  have h := QiushiMatmul.orbit38_lb12_mono
  change QuotientRankAtLeast (spanCodes [288, 128, 20, 8, 2, 1]) 12 at h
  exact bind_exact
    [288, 128, 20, 8, 2, 1] [288, 128, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep039 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 39))
      (frozenWangTable.lower 39) := by
  rw [show frozenWangTable.basis 39 = [256, 160, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 39 = 12 by decide]
  have h := QiushiMatmul.orbit39_lb12_mono
  change QuotientRankAtLeast (spanCodes [256, 160, 20, 8, 2, 1]) 12 at h
  exact bind_exact
    [256, 160, 20, 8, 2, 1] [256, 160, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep040 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 40))
      (frozenWangTable.lower 40) := by
  rw [show frozenWangTable.basis 40 = [128, 84, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 40 = 12 by decide]
  have h := QiushiMatmul.orbit40_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 32, 84, 128]) 12 at h
  exact bind_exact
    [128, 84, 32, 8, 2, 1] [1, 2, 8, 32, 84, 128] h
    (by decide) (by decide) (by decide)

theorem rep041 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 41))
      (frozenWangTable.lower 41) := by
  rw [show frozenWangTable.basis 41 = [384, 84, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 41 = 12 by decide]
  have h := QiushiMatmul.orbit41_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 32, 84, 384]) 12 at h
  exact bind_exact
    [384, 84, 32, 8, 2, 1] [1, 2, 8, 32, 84, 384] h
    (by decide) (by decide) (by decide)

theorem rep042 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 42))
      (frozenWangTable.lower 42) := by
  rw [show frozenWangTable.basis 42 = [256, 128, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 42 = 9 by decide]
  have h := QiushiMatmul.flatSeed_42
  change QuotientRankAtLeast (spanCodes [256, 128, 32, 8, 2, 1]) 9 at h
  exact bind_exact
    [256, 128, 32, 8, 2, 1] [256, 128, 32, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep043 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 43))
      (frozenWangTable.lower 43) := by
  rw [show frozenWangTable.basis 43 = [272, 128, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 43 = 12 by decide]
  have h := QiushiMatmul.orbit43_lb12_mono
  change QuotientRankAtLeast (spanCodes [272, 128, 32, 8, 2, 1]) 12 at h
  exact bind_exact
    [272, 128, 32, 8, 2, 1] [272, 128, 32, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep044 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 44))
      (frozenWangTable.lower 44) := by
  rw [show frozenWangTable.basis 44 = [272, 132, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 44 = 12 by decide]
  have h := QiushiMatmul.orbit44_lb12_mono
  change QuotientRankAtLeast (spanCodes [272, 132, 32, 8, 2, 1]) 12 at h
  exact bind_exact
    [272, 132, 32, 8, 2, 1] [272, 132, 32, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep045 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 45))
      (frozenWangTable.lower 45) := by
  rw [show frozenWangTable.basis 45 = [256, 160, 68, 8, 2, 1] by decide,
      show frozenWangTable.lower 45 = 13 by decide]
  have h := QiushiMatmul.step109_orbit45_lb13_wc
  change QuotientRankAtLeast (spanCodes [256, 160, 68, 8, 2, 1]) 13 at h
  exact bind_exact
    [256, 160, 68, 8, 2, 1] [256, 160, 68, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep046 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 46))
      (frozenWangTable.lower 46) := by
  rw [show frozenWangTable.basis 46 = [288, 160, 68, 8, 2, 1] by decide,
      show frozenWangTable.lower 46 = 12 by decide]
  have h := QiushiMatmul.plane472GenBound0178
  change QuotientRankAtLeast (spanCodes [288, 160, 68, 16, 8, 2, 1]) 12 at h
  exact bind_contained
    [288, 160, 68, 8, 2, 1] [288, 160, 68, 16, 8, 2, 1] h
    (by decide) (by decide)

theorem rep047 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 47))
      (frozenWangTable.lower 47) := by
  rw [show frozenWangTable.basis 47 = [304, 160, 68, 8, 2, 1] by decide,
      show frozenWangTable.lower 47 = 14 by decide]
  have h := QiushiMatmul.step109wc202s9Dispatch
  change QuotientRankAtLeast (spanCodes [304, 160, 68, 8, 2, 1]) 14 at h
  exact bind_exact
    [304, 160, 68, 8, 2, 1] [304, 160, 68, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep048 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 48))
      (frozenWangTable.lower 48) := by
  rw [show frozenWangTable.basis 48 = [256, 160, 84, 8, 2, 1] by decide,
      show frozenWangTable.lower 48 = 12 by decide]
  have h := QiushiMatmul.orbit10_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 16, 68, 160, 256]) 12 at h
  exact bind_contained
    [256, 160, 84, 8, 2, 1] [1, 2, 8, 16, 68, 160, 256] h
    (by decide) (by decide)

theorem rep049 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 49))
      (frozenWangTable.lower 49) := by
  rw [show frozenWangTable.basis 49 = [256, 132, 96, 8, 2, 1] by decide,
      show frozenWangTable.lower 49 = 12 by decide]
  have h := QiushiMatmul.orbit49_lb12_mono
  change QuotientRankAtLeast (spanCodes [256, 132, 96, 8, 2, 1]) 12 at h
  exact bind_exact
    [256, 132, 96, 8, 2, 1] [256, 132, 96, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep050 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 50))
      (frozenWangTable.lower 50) := by
  rw [show frozenWangTable.basis 50 = [272, 132, 96, 8, 2, 1] by decide,
      show frozenWangTable.lower 50 = 13 by decide]
  have h := QiushiMatmul.step109wc212s13Dispatch
  change QuotientRankAtLeast (spanCodes [272, 132, 96, 8, 2, 1]) 13 at h
  exact bind_exact
    [272, 132, 96, 8, 2, 1] [272, 132, 96, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep051 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 51))
      (frozenWangTable.lower 51) := by
  rw [show frozenWangTable.basis 51 = [148, 80, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 51 = 14 by decide]
  have h := QiushiMatmul.step109_orbit51_lb14_wc
  change QuotientRankAtLeast (spanCodes [148, 80, 32, 12, 2, 1]) 14 at h
  exact bind_exact
    [148, 80, 32, 12, 2, 1] [148, 80, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep052 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 52))
      (frozenWangTable.lower 52) := by
  rw [show frozenWangTable.basis 52 = [256, 80, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 52 = 12 by decide]
  have h := QiushiMatmul.step109wc119s7Dispatch
  change QuotientRankAtLeast (spanCodes [256, 132, 80, 32, 12, 2, 1]) 12 at h
  exact bind_contained
    [256, 80, 32, 12, 2, 1] [256, 132, 80, 32, 12, 2, 1] h
    (by decide) (by decide)

theorem rep053 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 53))
      (frozenWangTable.lower 53) := by
  rw [show frozenWangTable.basis 53 = [384, 80, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 53 = 12 by decide]
  have h := QiushiMatmul.orbit53_lb12_mono
  change QuotientRankAtLeast (spanCodes [384, 80, 32, 12, 2, 1]) 12 at h
  exact bind_exact
    [384, 80, 32, 12, 2, 1] [384, 80, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep054 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 54))
      (frozenWangTable.lower 54) := by
  rw [show frozenWangTable.basis 54 = [256, 132, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 54 = 12 by decide]
  have h := QiushiMatmul.step109wc119s3Dispatch
  change QuotientRankAtLeast (spanCodes [256, 132, 32, 16, 12, 2, 1]) 12 at h
  exact bind_contained
    [256, 132, 32, 12, 2, 1] [256, 132, 32, 16, 12, 2, 1] h
    (by decide) (by decide)

theorem rep055 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 55))
      (frozenWangTable.lower 55) := by
  rw [show frozenWangTable.basis 55 = [272, 132, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 55 = 14 by decide]
  have h := QiushiMatmul.step113_262_row11_qr
  change QuotientRankAtLeast (spanCodes [272, 132, 32, 12, 2, 1]) 14 at h
  exact bind_exact
    [272, 132, 32, 12, 2, 1] [272, 132, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep056 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 56))
      (frozenWangTable.lower 56) := by
  rw [show frozenWangTable.basis 56 = [256, 160, 80, 12, 2, 1] by decide,
      show frozenWangTable.lower 56 = 14 by decide]
  have h := QiushiMatmul.plane274GenBound0011
  change QuotientRankAtLeast (spanCodes [256, 160, 80, 12, 2, 1]) 14 at h
  exact bind_exact
    [256, 160, 80, 12, 2, 1] [256, 160, 80, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep057 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 57))
      (frozenWangTable.lower 57) := by
  rw [show frozenWangTable.basis 57 = [272, 132, 96, 12, 2, 1] by decide,
      show frozenWangTable.lower 57 = 14 by decide]
  have h := QiushiMatmul.step109wc127s0Dispatch
  change QuotientRankAtLeast (spanCodes [272, 132, 96, 12, 2, 1]) 14 at h
  exact bind_exact
    [272, 132, 96, 12, 2, 1] [272, 132, 96, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep058 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 58))
      (frozenWangTable.lower 58) := by
  rw [show frozenWangTable.basis 58 = [256, 152, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 58 = 12 by decide]
  have h := QiushiMatmul.step81o16s2Span_lb
  change QuotientRankAtLeast (spanCodes [256, 148, 80, 32, 12, 2, 1]) 12 at h
  exact bind_contained
    [256, 152, 80, 32, 2, 1] [256, 148, 80, 32, 12, 2, 1] h
    (by decide) (by decide)

theorem rep059 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 59))
      (frozenWangTable.lower 59) := by
  rw [show frozenWangTable.basis 59 = [264, 152, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 59 = 12 by decide]
  have h := QiushiMatmul.step109wc51s3Dispatch
  change QuotientRankAtLeast (spanCodes [260, 148, 80, 32, 12, 2, 1]) 12 at h
  exact bind_contained
    [264, 152, 80, 32, 2, 1] [260, 148, 80, 32, 12, 2, 1] h
    (by decide) (by decide)

theorem rep060 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 60))
      (frozenWangTable.lower 60) := by
  rw [show frozenWangTable.basis 60 = [256, 156, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 60 = 12 by decide]
  have h := QiushiMatmul.plane269GenBound0016
  change QuotientRankAtLeast (spanCodes [256, 148, 80, 32, 8, 2, 1]) 12 at h
  exact bind_contained
    [256, 156, 80, 32, 2, 1] [256, 148, 80, 32, 8, 2, 1] h
    (by decide) (by decide)

theorem rep061 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 61))
      (frozenWangTable.lower 61) := by
  rw [show frozenWangTable.basis 61 = [264, 156, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 61 = 12 by decide]
  have h := QiushiMatmul.plane269GenBound0016
  change QuotientRankAtLeast (spanCodes [256, 148, 80, 32, 8, 2, 1]) 12 at h
  exact bind_contained
    [264, 156, 80, 32, 2, 1] [256, 148, 80, 32, 8, 2, 1] h
    (by decide) (by decide)

theorem rep062 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 62))
      (frozenWangTable.lower 62) := by
  rw [show frozenWangTable.basis 62 = [272, 156, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 62 = 12 by decide]
  have h := QiushiMatmul.plane274GenBound0019
  change QuotientRankAtLeast (spanCodes [268, 128, 76, 32, 28, 2, 1]) 12 at h
  exact bind_contained
    [272, 156, 80, 32, 2, 1] [268, 128, 76, 32, 28, 2, 1] h
    (by decide) (by decide)

theorem rep063 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 63))
      (frozenWangTable.lower 63) := by
  rw [show frozenWangTable.basis 63 = [256, 160, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 63 = 14 by decide]
  have h := QiushiMatmul.step109wc147s8Dispatch
  change QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 10, 1]) 14 at h
  exact bind_exact
    [256, 160, 68, 16, 10, 1] [256, 160, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep064 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 64))
      (frozenWangTable.lower 64) := by
  rw [show frozenWangTable.basis 64 = [258, 160, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 64 = 15 by decide]
  have h := QiushiMatmul.step109wc204s0Dispatch
  change QuotientRankAtLeast (spanCodes [258, 160, 68, 16, 10, 1]) 15 at h
  exact bind_exact
    [258, 160, 68, 16, 10, 1] [258, 160, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep065 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 65))
      (frozenWangTable.lower 65) := by
  rw [show frozenWangTable.basis 65 = [260, 160, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 65 = 15 by decide]
  have h := QiushiMatmul.plane315GenBound0009
  change QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 10, 1]) 15 at h
  exact bind_exact
    [260, 160, 68, 16, 10, 1] [260, 160, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep066 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 66))
      (frozenWangTable.lower 66) := by
  rw [show frozenWangTable.basis 66 = [260, 164, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 66 = 12 by decide]
  have h := QiushiMatmul.plane487GenBound0550
  change QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 10, 4, 1]) 12 at h
  exact bind_contained
    [260, 164, 68, 16, 10, 1] [256, 160, 64, 16, 10, 4, 1] h
    (by decide) (by decide)

theorem rep067 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 67))
      (frozenWangTable.lower 67) := by
  rw [show frozenWangTable.basis 67 = [262, 164, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 67 = 15 by decide]
  have h := QiushiMatmul.step99_orbit67_lb15_unconditional
  change QuotientRankAtLeast (spanCodes [262, 164, 68, 16, 10, 1]) 15 at h
  exact bind_exact
    [262, 164, 68, 16, 10, 1] [262, 164, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep068 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 68))
      (frozenWangTable.lower 68) := by
  rw [show frozenWangTable.basis 68 = [288, 164, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 68 = 14 by decide]
  have h := QiushiMatmul.step99_orbit68_lb14_unconditional
  change QuotientRankAtLeast (spanCodes [288, 164, 68, 16, 10, 1]) 14 at h
  exact bind_exact
    [288, 164, 68, 16, 10, 1] [288, 164, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep069 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 69))
      (frozenWangTable.lower 69) := by
  rw [show frozenWangTable.basis 69 = [256, 164, 96, 16, 10, 1] by decide,
      show frozenWangTable.lower 69 = 15 by decide]
  have h := QiushiMatmul.plane152GenBound0001
  change QuotientRankAtLeast (spanCodes [256, 164, 96, 16, 10, 1]) 15 at h
  exact bind_exact
    [256, 164, 96, 16, 10, 1] [256, 164, 96, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep070 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 70))
      (frozenWangTable.lower 70) := by
  rw [show frozenWangTable.basis 70 = [258, 164, 96, 16, 10, 1] by decide,
      show frozenWangTable.lower 70 = 13 by decide]
  have h := QiushiMatmul.step109_orbit70_lb13_wc
  change QuotientRankAtLeast (spanCodes [258, 164, 96, 16, 10, 1]) 13 at h
  exact bind_exact
    [258, 164, 96, 16, 10, 1] [258, 164, 96, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep071 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 71))
      (frozenWangTable.lower 71) := by
  rw [show frozenWangTable.basis 71 = [128, 68, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 71 = 14 by decide]
  have h := QiushiMatmul.orbit71_lb14_mono
  change QuotientRankAtLeast (spanCodes [128, 68, 32, 20, 10, 1]) 14 at h
  exact bind_exact
    [128, 68, 32, 20, 10, 1] [128, 68, 32, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep072 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 72))
      (frozenWangTable.lower 72) := by
  rw [show frozenWangTable.basis 72 = [258, 68, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 72 = 15 by decide]
  have h := QiushiMatmul.step109wc156s1Dispatch
  change QuotientRankAtLeast (spanCodes [258, 68, 32, 20, 10, 1]) 15 at h
  exact bind_exact
    [258, 68, 32, 20, 10, 1] [258, 68, 32, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep073 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 73))
      (frozenWangTable.lower 73) := by
  rw [show frozenWangTable.basis 73 = [322, 192, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 73 = 12 by decide]
  have h := QiushiMatmul.step109wc83s4Dispatch
  change QuotientRankAtLeast (spanCodes [262, 132, 68, 32, 20, 10, 1]) 12 at h
  exact bind_contained
    [322, 192, 32, 20, 10, 1] [262, 132, 68, 32, 20, 10, 1] h
    (by decide) (by decide)

theorem rep074 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 74))
      (frozenWangTable.lower 74) := by
  rw [show frozenWangTable.basis 74 = [324, 192, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 74 = 14 by decide]
  have h := QiushiMatmul.orbit74_lb14_mono
  change QuotientRankAtLeast (spanCodes [324, 192, 32, 20, 10, 1]) 14 at h
  exact bind_exact
    [324, 192, 32, 20, 10, 1] [324, 192, 32, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep075 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 75))
      (frozenWangTable.lower 75) := by
  rw [show frozenWangTable.basis 75 = [262, 160, 68, 20, 10, 1] by decide,
      show frozenWangTable.lower 75 = 16 by decide]
  have h := QiushiMatmul.step109_orbit75_lb16_wc
  change QuotientRankAtLeast (spanCodes [262, 160, 68, 20, 10, 1]) 16 at h
  exact bind_exact
    [262, 160, 68, 20, 10, 1] [262, 160, 68, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep076 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 76))
      (frozenWangTable.lower 76) := by
  rw [show frozenWangTable.basis 76 = [288, 160, 68, 20, 10, 1] by decide,
      show frozenWangTable.lower 76 = 15 by decide]
  have h := QiushiMatmul.step109wc161s4Dispatch
  change QuotientRankAtLeast (spanCodes [288, 160, 68, 20, 10, 1]) 15 at h
  exact bind_exact
    [288, 160, 68, 20, 10, 1] [288, 160, 68, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep077 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 77))
      (frozenWangTable.lower 77) := by
  rw [show frozenWangTable.basis 77 = [260, 128, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 77 = 15 by decide]
  have h := QiushiMatmul.step99_orbit77_lb15_unconditional
  change QuotientRankAtLeast (spanCodes [260, 128, 96, 20, 10, 1]) 15 at h
  exact bind_exact
    [260, 128, 96, 20, 10, 1] [260, 128, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep078 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 78))
      (frozenWangTable.lower 78) := by
  rw [show frozenWangTable.basis 78 = [262, 128, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 78 = 14 by decide]
  have h := QiushiMatmul.step109_orbit78_lb14_wc
  change QuotientRankAtLeast (spanCodes [262, 128, 96, 20, 10, 1]) 14 at h
  exact bind_exact
    [262, 128, 96, 20, 10, 1] [262, 128, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep079 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 79))
      (frozenWangTable.lower 79) := by
  rw [show frozenWangTable.basis 79 = [258, 160, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 79 = 14 by decide]
  have h := QiushiMatmul.step109_orbit79_lb14_wc
  change QuotientRankAtLeast (spanCodes [258, 160, 96, 20, 10, 1]) 14 at h
  exact bind_exact
    [258, 160, 96, 20, 10, 1] [258, 160, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep080 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 80))
      (frozenWangTable.lower 80) := by
  rw [show frozenWangTable.basis 80 = [260, 160, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 80 = 15 by decide]
  have h := QiushiMatmul.plane315GenBound0017
  change QuotientRankAtLeast (spanCodes [260, 160, 96, 20, 10, 1]) 15 at h
  exact bind_exact
    [260, 160, 96, 20, 10, 1] [260, 160, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep081 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 81))
      (frozenWangTable.lower 81) := by
  rw [show frozenWangTable.basis 81 = [290, 160, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 81 = 15 by decide]
  have h := QiushiMatmul.step109wc166s6Dispatch
  change QuotientRankAtLeast (spanCodes [290, 160, 96, 20, 10, 1]) 15 at h
  exact bind_exact
    [290, 160, 96, 20, 10, 1] [290, 160, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep082 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 82))
      (frozenWangTable.lower 82) := by
  rw [show frozenWangTable.basis 82 = [292, 160, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 82 = 14 by decide]
  have h := QiushiMatmul.step99_orbit82_lb14_unconditional
  change QuotientRankAtLeast (spanCodes [292, 160, 96, 20, 10, 1]) 14 at h
  exact bind_exact
    [292, 160, 96, 20, 10, 1] [292, 160, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep083 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 83))
      (frozenWangTable.lower 83) := by
  rw [show frozenWangTable.basis 83 = [274, 144, 68, 32, 10, 1] by decide,
      show frozenWangTable.lower 83 = 14 by decide]
  have h := QiushiMatmul.step109wc204s4Dispatch
  change QuotientRankAtLeast (spanCodes [274, 144, 68, 32, 10, 1]) 14 at h
  exact bind_exact
    [274, 144, 68, 32, 10, 1] [274, 144, 68, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep084 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 84))
      (frozenWangTable.lower 84) := by
  rw [show frozenWangTable.basis 84 = [258, 128, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 84 = 14 by decide]
  have h := QiushiMatmul.step109wc179s0Dispatch
  change QuotientRankAtLeast (spanCodes [258, 128, 84, 32, 10, 1]) 14 at h
  exact bind_exact
    [258, 128, 84, 32, 10, 1] [258, 128, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep085 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 85))
      (frozenWangTable.lower 85) := by
  rw [show frozenWangTable.basis 85 = [262, 131, 68, 35, 20, 10] by decide,
      show frozenWangTable.lower 85 = 17 by decide]
  have h := QiushiMatmul.step109_orbit85_lb17_wc
  change QuotientRankAtLeast (spanCodes [262, 131, 68, 35, 20, 10]) 17 at h
  exact bind_exact
    [262, 131, 68, 35, 20, 10] [262, 131, 68, 35, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep086 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 86))
      (frozenWangTable.lower 86) := by
  rw [show frozenWangTable.basis 86 = [16, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 86 = 12 by decide]
  have h := QiushiMatmul.FrozenRegistry.Seed020.qra12
  change QuotientRankAtLeast (spanCodes [96, 16, 8, 4, 2, 1]) 12 at h
  exact bind_contained
    [16, 8, 4, 2, 1] [96, 16, 8, 4, 2, 1] h
    (by decide) (by decide)

theorem rep087 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 87))
      (frozenWangTable.lower 87) := by
  rw [show frozenWangTable.basis 87 = [64, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 87 = 11 by decide]
  have h := QiushiMatmul.GlobalOrbit.Unused.node87_bound
  change QuotientRankAtLeast (spanCodes [64, 8, 4, 2, 1]) 11 at h
  exact bind_exact
    [64, 8, 4, 2, 1] [64, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep088 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 88))
      (frozenWangTable.lower 88) := by
  rw [show frozenWangTable.basis 88 = [80, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 88 = 13 by decide]
  have h := QiushiMatmul.plane88UnusedGen_lb13
  change QuotientRankAtLeast (spanCodes [80, 8, 4, 2, 1]) 13 at h
  exact bind_exact
    [80, 8, 4, 2, 1] [80, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep089 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 89))
      (frozenWangTable.lower 89) := by
  rw [show frozenWangTable.basis 89 = [128, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 89 = 12 by decide]
  have h := QiushiMatmul.orbit89_lb12_mono
  change QuotientRankAtLeast (spanCodes [128, 8, 4, 2, 1]) 12 at h
  exact bind_exact
    [128, 8, 4, 2, 1] [128, 8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep090 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 90))
      (frozenWangTable.lower 90) := by
  rw [show frozenWangTable.basis 90 = [160, 8, 4, 2, 1] by decide,
      show frozenWangTable.lower 90 = 12 by decide]
  exact Transport.bound090

theorem rep091 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 91))
      (frozenWangTable.lower 91) := by
  rw [show frozenWangTable.basis 91 = [152, 80, 4, 2, 1] by decide,
      show frozenWangTable.lower 91 = 12 by decide]
  exact Transport.bound091

theorem rep092 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 92))
      (frozenWangTable.lower 92) := by
  rw [show frozenWangTable.basis 92 = [160, 80, 4, 2, 1] by decide,
      show frozenWangTable.lower 92 = 13 by decide]
  have h := QiushiMatmul.plane92UnusedGen_lb13
  change QuotientRankAtLeast (spanCodes [160, 80, 4, 2, 1]) 13 at h
  exact bind_exact
    [160, 80, 4, 2, 1] [160, 80, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep093 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 93))
      (frozenWangTable.lower 93) := by
  rw [show frozenWangTable.basis 93 = [68, 16, 8, 2, 1] by decide,
      show frozenWangTable.lower 93 = 15 by decide]
  have h := QiushiMatmul.orbit93_lb15_mono
  change QuotientRankAtLeast (spanCodes [68, 16, 8, 2, 1]) 15 at h
  exact bind_exact
    [68, 16, 8, 2, 1] [68, 16, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep094 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 94))
      (frozenWangTable.lower 94) := by
  rw [show frozenWangTable.basis 94 = [256, 16, 8, 2, 1] by decide,
      show frozenWangTable.lower 94 = 12 by decide]
  have h := QiushiMatmul.plane282GenSource0046
  change QuotientRankAtLeast (spanCodes [256, 196, 16, 8, 2, 1]) 12 at h
  exact bind_contained
    [256, 16, 8, 2, 1] [256, 196, 16, 8, 2, 1] h
    (by decide) (by decide)

theorem rep095 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 95))
      (frozenWangTable.lower 95) := by
  rw [show frozenWangTable.basis 95 = [32, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 95 = 15 by decide]
  have h := QiushiMatmul.orbit95_lb15_mono
  change QuotientRankAtLeast (spanCodes [32, 20, 8, 2, 1]) 15 at h
  exact bind_exact
    [32, 20, 8, 2, 1] [32, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep096 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 96))
      (frozenWangTable.lower 96) := by
  rw [show frozenWangTable.basis 96 = [68, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 96 = 16 by decide]
  have h := QiushiMatmul.step109_orbit96_lb16_wc
  change QuotientRankAtLeast (spanCodes [68, 20, 8, 2, 1]) 16 at h
  exact bind_exact
    [68, 20, 8, 2, 1] [68, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep097 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 97))
      (frozenWangTable.lower 97) := by
  rw [show frozenWangTable.basis 97 = [96, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 97 = 15 by decide]
  have h := QiushiMatmul.orbit97_lb15_mono
  change QuotientRankAtLeast (spanCodes [96, 20, 8, 2, 1]) 15 at h
  exact bind_exact
    [96, 20, 8, 2, 1] [96, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep098 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 98))
      (frozenWangTable.lower 98) := by
  rw [show frozenWangTable.basis 98 = [128, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 98 = 15 by decide]
  have h := QiushiMatmul.orbit98_lb15_mono
  change QuotientRankAtLeast (spanCodes [128, 20, 8, 2, 1]) 15 at h
  exact bind_exact
    [128, 20, 8, 2, 1] [128, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep099 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 99))
      (frozenWangTable.lower 99) := by
  rw [show frozenWangTable.basis 99 = [160, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 99 = 15 by decide]
  have h := QiushiMatmul.orbit99_lb15_mono
  change QuotientRankAtLeast (spanCodes [160, 20, 8, 2, 1]) 15 at h
  exact bind_exact
    [160, 20, 8, 2, 1] [160, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep100 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 100))
      (frozenWangTable.lower 100) := by
  rw [show frozenWangTable.basis 100 = [256, 20, 8, 2, 1] by decide,
      show frozenWangTable.lower 100 = 14 by decide]
  have h := QiushiMatmul.orbit100_lb14_mono
  change QuotientRankAtLeast (spanCodes [256, 20, 8, 2, 1]) 14 at h
  exact bind_exact
    [256, 20, 8, 2, 1] [256, 20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep101 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 101))
      (frozenWangTable.lower 101) := by
  rw [show frozenWangTable.basis 101 = [84, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 101 = 15 by decide]
  have h := QiushiMatmul.orbit101_lb15
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 32, 84]) 15 at h
  exact bind_exact
    [84, 32, 8, 2, 1] [1, 2, 8, 32, 84] h
    (by decide) (by decide) (by decide)

theorem rep102 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 102))
      (frozenWangTable.lower 102) := by
  rw [show frozenWangTable.basis 102 = [128, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 102 = 12 by decide]
  have h := QiushiMatmul.orbit102_lb12_mono
  change QuotientRankAtLeast (spanCodes [128, 32, 8, 2, 1]) 12 at h
  exact bind_exact
    [128, 32, 8, 2, 1] [128, 32, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep103 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 103))
      (frozenWangTable.lower 103) := by
  rw [show frozenWangTable.basis 103 = [132, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 103 = 15 by decide]
  have h := QiushiMatmul.orbit103_lb15_mono
  change QuotientRankAtLeast (spanCodes [132, 32, 8, 2, 1]) 15 at h
  exact bind_exact
    [132, 32, 8, 2, 1] [132, 32, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep104 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 104))
      (frozenWangTable.lower 104) := by
  rw [show frozenWangTable.basis 104 = [384, 32, 8, 2, 1] by decide,
      show frozenWangTable.lower 104 = 12 by decide]
  have h := QiushiMatmul.orbit41_lb12
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 32, 84, 384]) 12 at h
  exact bind_contained
    [384, 32, 8, 2, 1] [1, 2, 8, 32, 84, 384] h
    (by decide) (by decide)

theorem rep105 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 105))
      (frozenWangTable.lower 105) := by
  rw [show frozenWangTable.basis 105 = [160, 68, 8, 2, 1] by decide,
      show frozenWangTable.lower 105 = 15 by decide]
  have h := QiushiMatmul.orbit29_lb15
  change QuotientRankAtLeast (spanCodes [1, 2, 8, 16, 68, 160]) 15 at h
  exact bind_contained
    [160, 68, 8, 2, 1] [1, 2, 8, 16, 68, 160] h
    (by decide) (by decide)

theorem rep106 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 106))
      (frozenWangTable.lower 106) := by
  rw [show frozenWangTable.basis 106 = [256, 68, 8, 2, 1] by decide,
      show frozenWangTable.lower 106 = 14 by decide]
  have h := QiushiMatmul.orbit106_lb14_mono
  change QuotientRankAtLeast (spanCodes [256, 68, 8, 2, 1]) 14 at h
  exact bind_exact
    [256, 68, 8, 2, 1] [256, 68, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep107 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 107))
      (frozenWangTable.lower 107) := by
  rw [show frozenWangTable.basis 107 = [272, 68, 8, 2, 1] by decide,
      show frozenWangTable.lower 107 = 15 by decide]
  have h := QiushiMatmul.plane426GenBound0076
  change QuotientRankAtLeast (spanCodes [272, 68, 36, 8, 2, 1]) 15 at h
  exact bind_contained
    [272, 68, 8, 2, 1] [272, 68, 36, 8, 2, 1] h
    (by decide) (by decide)

theorem rep108 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 108))
      (frozenWangTable.lower 108) := by
  rw [show frozenWangTable.basis 108 = [160, 84, 8, 2, 1] by decide,
      show frozenWangTable.lower 108 = 15 by decide]
  have h := QiushiMatmul.orbit108_lb15_mono
  change QuotientRankAtLeast (spanCodes [160, 84, 8, 2, 1]) 15 at h
  exact bind_exact
    [160, 84, 8, 2, 1] [160, 84, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep109 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 109))
      (frozenWangTable.lower 109) := by
  rw [show frozenWangTable.basis 109 = [256, 84, 8, 2, 1] by decide,
      show frozenWangTable.lower 109 = 14 by decide]
  have h := QiushiMatmul.FrozenRank.span109_lb14
  change QuotientRankAtLeast (spanCodes [256, 84, 8, 2, 1]) 14 at h
  exact bind_exact
    [256, 84, 8, 2, 1] [256, 84, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep110 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 110))
      (frozenWangTable.lower 110) := by
  rw [show frozenWangTable.basis 110 = [132, 96, 8, 2, 1] by decide,
      show frozenWangTable.lower 110 = 15 by decide]
  have h := QiushiMatmul.orbit110_lb15_mono
  change QuotientRankAtLeast (spanCodes [132, 96, 8, 2, 1]) 15 at h
  exact bind_exact
    [132, 96, 8, 2, 1] [132, 96, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep111 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 111))
      (frozenWangTable.lower 111) := by
  rw [show frozenWangTable.basis 111 = [256, 96, 8, 2, 1] by decide,
      show frozenWangTable.lower 111 = 14 by decide]
  have h := QiushiMatmul.step109_orbit111_lb14_wc
  change QuotientRankAtLeast (spanCodes [256, 96, 8, 2, 1]) 14 at h
  exact bind_exact
    [256, 96, 8, 2, 1] [256, 96, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep112 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 112))
      (frozenWangTable.lower 112) := by
  rw [show frozenWangTable.basis 112 = [272, 96, 8, 2, 1] by decide,
      show frozenWangTable.lower 112 = 15 by decide]
  have h := QiushiMatmul.orbit112_lb15_mono
  change QuotientRankAtLeast (spanCodes [272, 96, 8, 2, 1]) 15 at h
  exact bind_exact
    [272, 96, 8, 2, 1] [272, 96, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep113 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 113))
      (frozenWangTable.lower 113) := by
  rw [show frozenWangTable.basis 113 = [384, 96, 8, 2, 1] by decide,
      show frozenWangTable.lower 113 = 14 by decide]
  have h := QiushiMatmul.step109_orbit113_lb14_wc
  change QuotientRankAtLeast (spanCodes [384, 96, 8, 2, 1]) 14 at h
  exact bind_exact
    [384, 96, 8, 2, 1] [384, 96, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep114 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 114))
      (frozenWangTable.lower 114) := by
  rw [show frozenWangTable.basis 114 = [256, 160, 8, 2, 1] by decide,
      show frozenWangTable.lower 114 = 14 by decide]
  have h := QiushiMatmul.step109_orbit114_lb14_wc
  change QuotientRankAtLeast (spanCodes [256, 160, 8, 2, 1]) 14 at h
  exact bind_exact
    [256, 160, 8, 2, 1] [256, 160, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep115 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 115))
      (frozenWangTable.lower 115) := by
  rw [show frozenWangTable.basis 115 = [288, 160, 8, 2, 1] by decide,
      show frozenWangTable.lower 115 = 12 by decide]
  have h := QiushiMatmul.step109wc113s5Dispatch
  change QuotientRankAtLeast (spanCodes [288, 160, 96, 8, 2, 1]) 12 at h
  exact bind_contained
    [288, 160, 8, 2, 1] [288, 160, 96, 8, 2, 1] h
    (by decide) (by decide)

theorem rep116 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 116))
      (frozenWangTable.lower 116) := by
  rw [show frozenWangTable.basis 116 = [304, 160, 8, 2, 1] by decide,
      show frozenWangTable.lower 116 = 14 by decide]
  have h := QiushiMatmul.orbit116_lb14_mono
  change QuotientRankAtLeast (spanCodes [304, 160, 8, 2, 1]) 14 at h
  exact bind_exact
    [304, 160, 8, 2, 1] [304, 160, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep117 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 117))
      (frozenWangTable.lower 117) := by
  rw [show frozenWangTable.basis 117 = [80, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 117 = 14 by decide]
  have h := QiushiMatmul.step109_orbit51_lb14_wc
  change QuotientRankAtLeast (spanCodes [148, 80, 32, 12, 2, 1]) 14 at h
  exact bind_contained
    [80, 32, 12, 2, 1] [148, 80, 32, 12, 2, 1] h
    (by decide) (by decide)

theorem rep118 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 118))
      (frozenWangTable.lower 118) := by
  rw [show frozenWangTable.basis 118 = [132, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 118 = 15 by decide]
  have h := QiushiMatmul.orbit118_lb15_mono
  change QuotientRankAtLeast (spanCodes [132, 32, 12, 2, 1]) 15 at h
  exact bind_exact
    [132, 32, 12, 2, 1] [132, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep119 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 119))
      (frozenWangTable.lower 119) := by
  rw [show frozenWangTable.basis 119 = [256, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 119 = 14 by decide]
  have h := QiushiMatmul.step109_orbit119_lb14_wc
  change QuotientRankAtLeast (spanCodes [256, 32, 12, 2, 1]) 14 at h
  exact bind_exact
    [256, 32, 12, 2, 1] [256, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep120 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 120))
      (frozenWangTable.lower 120) := by
  rw [show frozenWangTable.basis 120 = [272, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 120 = 15 by decide]
  have h := QiushiMatmul.step99_orbit120_lb15_unconditional
  change QuotientRankAtLeast (spanCodes [272, 32, 12, 2, 1]) 15 at h
  exact bind_exact
    [272, 32, 12, 2, 1] [272, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep121 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 121))
      (frozenWangTable.lower 121) := by
  rw [show frozenWangTable.basis 121 = [384, 32, 12, 2, 1] by decide,
      show frozenWangTable.lower 121 = 14 by decide]
  have h := QiushiMatmul.orbit121_lb14_mono
  change QuotientRankAtLeast (spanCodes [384, 32, 12, 2, 1]) 14 at h
  exact bind_exact
    [384, 32, 12, 2, 1] [384, 32, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep122 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 122))
      (frozenWangTable.lower 122) := by
  rw [show frozenWangTable.basis 122 = [148, 80, 12, 2, 1] by decide,
      show frozenWangTable.lower 122 = 15 by decide]
  exact Transport.bound122

theorem rep123 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 123))
      (frozenWangTable.lower 123) := by
  rw [show frozenWangTable.basis 123 = [160, 80, 12, 2, 1] by decide,
      show frozenWangTable.lower 123 = 15 by decide]
  have h := QiushiMatmul.orbit123_lb15_mono
  change QuotientRankAtLeast (spanCodes [160, 80, 12, 2, 1]) 15 at h
  exact bind_exact
    [160, 80, 12, 2, 1] [160, 80, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep124 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 124))
      (frozenWangTable.lower 124) := by
  rw [show frozenWangTable.basis 124 = [256, 80, 12, 2, 1] by decide,
      show frozenWangTable.lower 124 = 15 by decide]
  have h := QiushiMatmul.orbit124_lb15_mono
  change QuotientRankAtLeast (spanCodes [256, 80, 12, 2, 1]) 15 at h
  exact bind_exact
    [256, 80, 12, 2, 1] [256, 80, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep125 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 125))
      (frozenWangTable.lower 125) := by
  rw [show frozenWangTable.basis 125 = [132, 96, 12, 2, 1] by decide,
      show frozenWangTable.lower 125 = 15 by decide]
  have h := QiushiMatmul.orbit125_lb15_mono
  change QuotientRankAtLeast (spanCodes [132, 96, 12, 2, 1]) 15 at h
  exact bind_exact
    [132, 96, 12, 2, 1] [132, 96, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep126 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 126))
      (frozenWangTable.lower 126) := by
  rw [show frozenWangTable.basis 126 = [256, 96, 12, 2, 1] by decide,
      show frozenWangTable.lower 126 = 14 by decide]
  have h := QiushiMatmul.orbit126_lb14_mono
  change QuotientRankAtLeast (spanCodes [256, 96, 12, 2, 1]) 14 at h
  exact bind_exact
    [256, 96, 12, 2, 1] [256, 96, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep127 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 127))
      (frozenWangTable.lower 127) := by
  rw [show frozenWangTable.basis 127 = [272, 96, 12, 2, 1] by decide,
      show frozenWangTable.lower 127 = 15 by decide]
  have h := QiushiMatmul.step109_orbit127_lb15_wc
  change QuotientRankAtLeast (spanCodes [272, 96, 12, 2, 1]) 15 at h
  exact bind_exact
    [272, 96, 12, 2, 1] [272, 96, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep128 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 128))
      (frozenWangTable.lower 128) := by
  rw [show frozenWangTable.basis 128 = [384, 96, 12, 2, 1] by decide,
      show frozenWangTable.lower 128 = 15 by decide]
  have h := QiushiMatmul.step109_orbit128_lb15_wc
  change QuotientRankAtLeast (spanCodes [384, 96, 12, 2, 1]) 15 at h
  exact bind_exact
    [384, 96, 12, 2, 1] [384, 96, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep129 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 129))
      (frozenWangTable.lower 129) := by
  rw [show frozenWangTable.basis 129 = [288, 132, 12, 2, 1] by decide,
      show frozenWangTable.lower 129 = 15 by decide]
  have h := QiushiMatmul.orbit129_lb15_mono
  change QuotientRankAtLeast (spanCodes [288, 132, 12, 2, 1]) 15 at h
  exact bind_exact
    [288, 132, 12, 2, 1] [288, 132, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep130 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 130))
      (frozenWangTable.lower 130) := by
  rw [show frozenWangTable.basis 130 = [256, 160, 12, 2, 1] by decide,
      show frozenWangTable.lower 130 = 15 by decide]
  have h := QiushiMatmul.orbit130_lb15_mono
  change QuotientRankAtLeast (spanCodes [256, 160, 12, 2, 1]) 15 at h
  exact bind_exact
    [256, 160, 12, 2, 1] [256, 160, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep131 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 131))
      (frozenWangTable.lower 131) := by
  rw [show frozenWangTable.basis 131 = [288, 160, 12, 2, 1] by decide,
      show frozenWangTable.lower 131 = 14 by decide]
  have h := QiushiMatmul.orbit131_lb14_mono
  change QuotientRankAtLeast (spanCodes [288, 160, 12, 2, 1]) 14 at h
  exact bind_exact
    [288, 160, 12, 2, 1] [288, 160, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep132 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 132))
      (frozenWangTable.lower 132) := by
  rw [show frozenWangTable.basis 132 = [304, 160, 12, 2, 1] by decide,
      show frozenWangTable.lower 132 = 15 by decide]
  have h := QiushiMatmul.step109_orbit132_lb15_wc
  change QuotientRankAtLeast (spanCodes [304, 160, 12, 2, 1]) 15 at h
  exact bind_exact
    [304, 160, 12, 2, 1] [304, 160, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep133 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 133))
      (frozenWangTable.lower 133) := by
  rw [show frozenWangTable.basis 133 = [152, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 133 = 14 by decide]
  have h := QiushiMatmul.step109_orbit51_lb14_wc
  change QuotientRankAtLeast (spanCodes [148, 80, 32, 12, 2, 1]) 14 at h
  exact bind_contained
    [152, 80, 32, 2, 1] [148, 80, 32, 12, 2, 1] h
    (by decide) (by decide)

theorem rep134 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 134))
      (frozenWangTable.lower 134) := by
  rw [show frozenWangTable.basis 134 = [156, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 134 = 15 by decide]
  have h := QiushiMatmul.orbit134_lb15_mono
  change QuotientRankAtLeast (spanCodes [156, 80, 32, 2, 1]) 15 at h
  exact bind_exact
    [156, 80, 32, 2, 1] [156, 80, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep135 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 135))
      (frozenWangTable.lower 135) := by
  rw [show frozenWangTable.basis 135 = [256, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 135 = 12 by decide]
  have h := QiushiMatmul.plane269GenBound0016
  change QuotientRankAtLeast (spanCodes [256, 148, 80, 32, 8, 2, 1]) 12 at h
  exact bind_contained
    [256, 80, 32, 2, 1] [256, 148, 80, 32, 8, 2, 1] h
    (by decide) (by decide)

theorem rep136 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 136))
      (frozenWangTable.lower 136) := by
  rw [show frozenWangTable.basis 136 = [264, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 136 = 14 by decide]
  exact Transport.bound136

theorem rep137 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 137))
      (frozenWangTable.lower 137) := by
  rw [show frozenWangTable.basis 137 = [272, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 137 = 14 by decide]
  have h := QiushiMatmul.orbit137_lb14_mono
  change QuotientRankAtLeast (spanCodes [272, 80, 32, 2, 1]) 14 at h
  exact bind_exact
    [272, 80, 32, 2, 1] [272, 80, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep138 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 138))
      (frozenWangTable.lower 138) := by
  rw [show frozenWangTable.basis 138 = [400, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 138 = 12 by decide]
  have h := QiushiMatmul.plane274GenBound0019
  change QuotientRankAtLeast (spanCodes [268, 128, 76, 32, 28, 2, 1]) 12 at h
  exact bind_contained
    [400, 80, 32, 2, 1] [268, 128, 76, 32, 28, 2, 1] h
    (by decide) (by decide)

theorem rep139 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 139))
      (frozenWangTable.lower 139) := by
  rw [show frozenWangTable.basis 139 = [408, 80, 32, 2, 1] by decide,
      show frozenWangTable.lower 139 = 14 by decide]
  exact Transport.bound139

theorem rep140 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 140))
      (frozenWangTable.lower 140) := by
  rw [show frozenWangTable.basis 140 = [256, 84, 32, 2, 1] by decide,
      show frozenWangTable.lower 140 = 14 by decide]
  have h := QiushiMatmul.plane267GenBound0012
  change QuotientRankAtLeast (spanCodes [256, 84, 32, 2, 1]) 14 at h
  exact bind_exact
    [256, 84, 32, 2, 1] [256, 84, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep141 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 141))
      (frozenWangTable.lower 141) := by
  rw [show frozenWangTable.basis 141 = [264, 84, 32, 2, 1] by decide,
      show frozenWangTable.lower 141 = 15 by decide]
  have h := QiushiMatmul.plane269GenBound0004
  change QuotientRankAtLeast (spanCodes [264, 84, 32, 2, 1]) 15 at h
  exact bind_exact
    [264, 84, 32, 2, 1] [264, 84, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep142 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 142))
      (frozenWangTable.lower 142) := by
  rw [show frozenWangTable.basis 142 = [272, 84, 32, 2, 1] by decide,
      show frozenWangTable.lower 142 = 14 by decide]
  have h := QiushiMatmul.orbit142_lb14_mono
  change QuotientRankAtLeast (spanCodes [272, 84, 32, 2, 1]) 14 at h
  exact bind_exact
    [272, 84, 32, 2, 1] [272, 84, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep143 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 143))
      (frozenWangTable.lower 143) := by
  rw [show frozenWangTable.basis 143 = [400, 84, 32, 2, 1] by decide,
      show frozenWangTable.lower 143 = 14 by decide]
  have h := QiushiMatmul.plane267GenBound0013
  change QuotientRankAtLeast (spanCodes [400, 84, 32, 2, 1]) 14 at h
  exact bind_exact
    [400, 84, 32, 2, 1] [400, 84, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep144 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 144))
      (frozenWangTable.lower 144) := by
  rw [show frozenWangTable.basis 144 = [408, 84, 32, 2, 1] by decide,
      show frozenWangTable.lower 144 = 15 by decide]
  have h := QiushiMatmul.plane267GenBound0009
  change QuotientRankAtLeast (spanCodes [408, 84, 32, 2, 1]) 15 at h
  exact bind_exact
    [408, 84, 32, 2, 1] [408, 84, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep145 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 145))
      (frozenWangTable.lower 145) := by
  rw [show frozenWangTable.basis 145 = [280, 160, 80, 2, 1] by decide,
      show frozenWangTable.lower 145 = 14 by decide]
  have h := QiushiMatmul.plane274GenBound0015
  change QuotientRankAtLeast (spanCodes [280, 132, 80, 36, 2, 1]) 14 at h
  exact bind_contained
    [280, 160, 80, 2, 1] [280, 132, 80, 36, 2, 1] h
    (by decide) (by decide)

theorem rep146 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 146))
      (frozenWangTable.lower 146) := by
  rw [show frozenWangTable.basis 146 = [280, 160, 84, 2, 1] by decide,
      show frozenWangTable.lower 146 = 15 by decide]
  have h := QiushiMatmul.plane275GenBound0014
  change QuotientRankAtLeast (spanCodes [280, 160, 84, 2, 1]) 15 at h
  exact bind_exact
    [280, 160, 84, 2, 1] [280, 160, 84, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep147 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 147))
      (frozenWangTable.lower 147) := by
  rw [show frozenWangTable.basis 147 = [160, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 147 = 16 by decide]
  have h := QiushiMatmul.step109_orbit147_lb16_wc
  change QuotientRankAtLeast (spanCodes [160, 68, 16, 10, 1]) 16 at h
  exact bind_exact
    [160, 68, 16, 10, 1] [160, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep148 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 148))
      (frozenWangTable.lower 148) := by
  rw [show frozenWangTable.basis 148 = [164, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 148 = 15 by decide]
  have h := QiushiMatmul.orbit148_lb15_mono
  change QuotientRankAtLeast (spanCodes [164, 68, 16, 10, 1]) 15 at h
  exact bind_exact
    [164, 68, 16, 10, 1] [164, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep149 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 149))
      (frozenWangTable.lower 149) := by
  rw [show frozenWangTable.basis 149 = [256, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 149 = 15 by decide]
  have h := QiushiMatmul.orbit149_lb15_mono
  change QuotientRankAtLeast (spanCodes [256, 68, 16, 10, 1]) 15 at h
  exact bind_exact
    [256, 68, 16, 10, 1] [256, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep150 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 150))
      (frozenWangTable.lower 150) := by
  rw [show frozenWangTable.basis 150 = [258, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 150 = 16 by decide]
  have h := QiushiMatmul.plane469GenBound0003
  change QuotientRankAtLeast (spanCodes [258, 68, 16, 10, 1]) 16 at h
  exact bind_exact
    [258, 68, 16, 10, 1] [258, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep151 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 151))
      (frozenWangTable.lower 151) := by
  rw [show frozenWangTable.basis 151 = [288, 68, 16, 10, 1] by decide,
      show frozenWangTable.lower 151 = 15 by decide]
  have h := QiushiMatmul.orbit151_lb15_mono
  change QuotientRankAtLeast (spanCodes [288, 68, 16, 10, 1]) 15 at h
  exact bind_exact
    [288, 68, 16, 10, 1] [288, 68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep152 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 152))
      (frozenWangTable.lower 152) := by
  rw [show frozenWangTable.basis 152 = [164, 96, 16, 10, 1] by decide,
      show frozenWangTable.lower 152 = 16 by decide]
  have h := QiushiMatmul.plane152Gen_lb16
  change QuotientRankAtLeast (spanCodes [164, 96, 16, 10, 1]) 16 at h
  exact bind_exact
    [164, 96, 16, 10, 1] [164, 96, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep153 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 153))
      (frozenWangTable.lower 153) := by
  rw [show frozenWangTable.basis 153 = [256, 96, 16, 10, 1] by decide,
      show frozenWangTable.lower 153 = 15 by decide]
  have h := QiushiMatmul.step98_orbit153_lb15_unconditional
  change QuotientRankAtLeast (spanCodes [256, 96, 16, 10, 1]) 15 at h
  exact bind_exact
    [256, 96, 16, 10, 1] [256, 96, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep154 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 154))
      (frozenWangTable.lower 154) := by
  rw [show frozenWangTable.basis 154 = [288, 96, 16, 10, 1] by decide,
      show frozenWangTable.lower 154 = 14 by decide]
  exact Transport.bound154

theorem rep155 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 155))
      (frozenWangTable.lower 155) := by
  rw [show frozenWangTable.basis 155 = [290, 96, 16, 10, 1] by decide,
      show frozenWangTable.lower 155 = 15 by decide]
  have h := QiushiMatmul.plane152GenBound0003
  change QuotientRankAtLeast (spanCodes [290, 164, 96, 16, 10, 1]) 15 at h
  exact bind_contained
    [290, 96, 16, 10, 1] [290, 164, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep156 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 156))
      (frozenWangTable.lower 156) := by
  rw [show frozenWangTable.basis 156 = [68, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 156 = 16 by decide]
  have h := QiushiMatmul.plane419GenBound0005
  change QuotientRankAtLeast (spanCodes [68, 32, 20, 10, 1]) 16 at h
  exact bind_exact
    [68, 32, 20, 10, 1] [68, 32, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep157 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 157))
      (frozenWangTable.lower 157) := by
  rw [show frozenWangTable.basis 157 = [128, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 157 = 15 by decide]
  have h := QiushiMatmul.plane292GenBound0000
  change QuotientRankAtLeast (spanCodes [128, 32, 20, 10, 1]) 15 at h
  exact bind_exact
    [128, 32, 20, 10, 1] [128, 32, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep158 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 158))
      (frozenWangTable.lower 158) := by
  rw [show frozenWangTable.basis 158 = [192, 32, 20, 10, 1] by decide,
      show frozenWangTable.lower 158 = 15 by decide]
  have h := QiushiMatmul.orbit158_lb15_mono
  change QuotientRankAtLeast (spanCodes [192, 32, 20, 10, 1]) 15 at h
  exact bind_exact
    [192, 32, 20, 10, 1] [192, 32, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep159 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 159))
      (frozenWangTable.lower 159) := by
  rw [show frozenWangTable.basis 159 = [160, 68, 20, 10, 1] by decide,
      show frozenWangTable.lower 159 = 16 by decide]
  have h := QiushiMatmul.orbit159_lb16_mono
  change QuotientRankAtLeast (spanCodes [160, 68, 20, 10, 1]) 16 at h
  exact bind_exact
    [160, 68, 20, 10, 1] [160, 68, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep160 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 160))
      (frozenWangTable.lower 160) := by
  rw [show frozenWangTable.basis 160 = [258, 68, 20, 10, 1] by decide,
      show frozenWangTable.lower 160 = 16 by decide]
  have h := QiushiMatmul.orbit160_lb16_mono
  change QuotientRankAtLeast (spanCodes [258, 68, 20, 10, 1]) 16 at h
  exact bind_exact
    [258, 68, 20, 10, 1] [258, 68, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep161 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 161))
      (frozenWangTable.lower 161) := by
  rw [show frozenWangTable.basis 161 = [288, 68, 20, 10, 1] by decide,
      show frozenWangTable.lower 161 = 16 by decide]
  have h := QiushiMatmul.step109_orbit161_lb16_wc
  change QuotientRankAtLeast (spanCodes [288, 68, 20, 10, 1]) 16 at h
  exact bind_exact
    [288, 68, 20, 10, 1] [288, 68, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep162 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 162))
      (frozenWangTable.lower 162) := by
  rw [show frozenWangTable.basis 162 = [128, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 162 = 16 by decide]
  have h := QiushiMatmul.FrozenRank.span162_lb16
  change QuotientRankAtLeast (spanCodes [128, 96, 20, 10, 1]) 16 at h
  exact bind_exact
    [128, 96, 20, 10, 1] [128, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep163 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 163))
      (frozenWangTable.lower 163) := by
  rw [show frozenWangTable.basis 163 = [160, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 163 = 15 by decide]
  have h := QiushiMatmul.plane315GenBound0017
  change QuotientRankAtLeast (spanCodes [260, 160, 96, 20, 10, 1]) 15 at h
  exact bind_contained
    [160, 96, 20, 10, 1] [260, 160, 96, 20, 10, 1] h
    (by decide) (by decide)

theorem rep164 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 164))
      (frozenWangTable.lower 164) := by
  rw [show frozenWangTable.basis 164 = [256, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 164 = 16 by decide]
  have h := QiushiMatmul.step109_orbit164_lb16_wc
  change QuotientRankAtLeast (spanCodes [256, 96, 20, 10, 1]) 16 at h
  exact bind_exact
    [256, 96, 20, 10, 1] [256, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep165 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 165))
      (frozenWangTable.lower 165) := by
  rw [show frozenWangTable.basis 165 = [288, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 165 = 15 by decide]
  have h := QiushiMatmul.step109_orbit165_lb15_wc
  change QuotientRankAtLeast (spanCodes [288, 96, 20, 10, 1]) 15 at h
  exact bind_exact
    [288, 96, 20, 10, 1] [288, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep166 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 166))
      (frozenWangTable.lower 166) := by
  rw [show frozenWangTable.basis 166 = [290, 96, 20, 10, 1] by decide,
      show frozenWangTable.lower 166 = 16 by decide]
  have h := QiushiMatmul.step109_orbit166_lb16_wc
  change QuotientRankAtLeast (spanCodes [290, 96, 20, 10, 1]) 16 at h
  exact bind_exact
    [290, 96, 20, 10, 1] [290, 96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep167 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 167))
      (frozenWangTable.lower 167) := by
  rw [show frozenWangTable.basis 167 = [258, 128, 20, 10, 1] by decide,
      show frozenWangTable.lower 167 = 15 by decide]
  have h := QiushiMatmul.plane481GenBound0092
  change QuotientRankAtLeast (spanCodes [258, 128, 36, 20, 10, 1]) 15 at h
  exact bind_contained
    [258, 128, 20, 10, 1] [258, 128, 36, 20, 10, 1] h
    (by decide) (by decide)

theorem rep168 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 168))
      (frozenWangTable.lower 168) := by
  rw [show frozenWangTable.basis 168 = [260, 128, 20, 10, 1] by decide,
      show frozenWangTable.lower 168 = 15 by decide]
  have h := QiushiMatmul.orbit168_lb15_mono
  change QuotientRankAtLeast (spanCodes [260, 128, 20, 10, 1]) 15 at h
  exact bind_exact
    [260, 128, 20, 10, 1] [260, 128, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep169 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 169))
      (frozenWangTable.lower 169) := by
  rw [show frozenWangTable.basis 169 = [288, 128, 20, 10, 1] by decide,
      show frozenWangTable.lower 169 = 15 by decide]
  have h := QiushiMatmul.orbit169_lb15_mono
  change QuotientRankAtLeast (spanCodes [288, 128, 20, 10, 1]) 15 at h
  exact bind_exact
    [288, 128, 20, 10, 1] [288, 128, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep170 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 170))
      (frozenWangTable.lower 170) := by
  rw [show frozenWangTable.basis 170 = [292, 128, 20, 10, 1] by decide,
      show frozenWangTable.lower 170 = 14 by decide]
  exact Transport.bound170

theorem rep171 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 171))
      (frozenWangTable.lower 171) := by
  rw [show frozenWangTable.basis 171 = [294, 128, 20, 10, 1] by decide,
      show frozenWangTable.lower 171 = 15 by decide]
  have h := QiushiMatmul.plane481GenBound0092
  change QuotientRankAtLeast (spanCodes [258, 128, 36, 20, 10, 1]) 15 at h
  exact bind_contained
    [294, 128, 20, 10, 1] [258, 128, 36, 20, 10, 1] h
    (by decide) (by decide)

theorem rep172 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 172))
      (frozenWangTable.lower 172) := by
  rw [show frozenWangTable.basis 172 = [256, 160, 20, 10, 1] by decide,
      show frozenWangTable.lower 172 = 15 by decide]
  exact Transport.bound172

theorem rep173 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 173))
      (frozenWangTable.lower 173) := by
  rw [show frozenWangTable.basis 173 = [258, 160, 20, 10, 1] by decide,
      show frozenWangTable.lower 173 = 15 by decide]
  exact Transport.bound173

theorem rep174 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 174))
      (frozenWangTable.lower 174) := by
  rw [show frozenWangTable.basis 174 = [260, 160, 20, 10, 1] by decide,
      show frozenWangTable.lower 174 = 15 by decide]
  have h := QiushiMatmul.orbit174_lb15_mono
  change QuotientRankAtLeast (spanCodes [260, 160, 20, 10, 1]) 15 at h
  exact bind_exact
    [260, 160, 20, 10, 1] [260, 160, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep175 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 175))
      (frozenWangTable.lower 175) := by
  rw [show frozenWangTable.basis 175 = [262, 160, 20, 10, 1] by decide,
      show frozenWangTable.lower 175 = 16 by decide]
  have h := QiushiMatmul.orbit175_lb16_mono
  change QuotientRankAtLeast (spanCodes [262, 160, 20, 10, 1]) 16 at h
  exact bind_exact
    [262, 160, 20, 10, 1] [262, 160, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep176 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 176))
      (frozenWangTable.lower 176) := by
  rw [show frozenWangTable.basis 176 = [128, 68, 32, 10, 1] by decide,
      show frozenWangTable.lower 176 = 15 by decide]
  have h := QiushiMatmul.orbit176_lb15_mono
  change QuotientRankAtLeast (spanCodes [128, 68, 32, 10, 1]) 15 at h
  exact bind_exact
    [128, 68, 32, 10, 1] [128, 68, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep177 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 177))
      (frozenWangTable.lower 177) := by
  rw [show frozenWangTable.basis 177 = [144, 68, 32, 10, 1] by decide,
      show frozenWangTable.lower 177 = 15 by decide]
  have h := QiushiMatmul.orbit177_lb15_mono
  change QuotientRankAtLeast (spanCodes [144, 68, 32, 10, 1]) 15 at h
  exact bind_exact
    [144, 68, 32, 10, 1] [144, 68, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep178 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 178))
      (frozenWangTable.lower 178) := by
  rw [show frozenWangTable.basis 178 = [272, 68, 32, 10, 1] by decide,
      show frozenWangTable.lower 178 = 16 by decide]
  have h := QiushiMatmul.plane295GenBound0001
  change QuotientRankAtLeast (spanCodes [272, 68, 32, 10, 1]) 16 at h
  exact bind_exact
    [272, 68, 32, 10, 1] [272, 68, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep179 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 179))
      (frozenWangTable.lower 179) := by
  rw [show frozenWangTable.basis 179 = [128, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 179 = 15 by decide]
  have h := QiushiMatmul.plane292GenBound0006
  change QuotientRankAtLeast (spanCodes [128, 84, 32, 10, 1]) 15 at h
  exact bind_exact
    [128, 84, 32, 10, 1] [128, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep180 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 180))
      (frozenWangTable.lower 180) := by
  rw [show frozenWangTable.basis 180 = [144, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 180 = 15 by decide]
  have h := QiushiMatmul.step109_orbit180_lb15_wc
  change QuotientRankAtLeast (spanCodes [144, 84, 32, 10, 1]) 15 at h
  exact bind_exact
    [144, 84, 32, 10, 1] [144, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep181 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 181))
      (frozenWangTable.lower 181) := by
  rw [show frozenWangTable.basis 181 = [258, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 181 = 15 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound181
  change QuotientRankAtLeast (spanCodes [258, 84, 32, 10, 1]) 15 at h
  exact bind_exact
    [258, 84, 32, 10, 1] [258, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep182 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 182))
      (frozenWangTable.lower 182) := by
  rw [show frozenWangTable.basis 182 = [272, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 182 = 15 by decide]
  have h := QiushiMatmul.orbit182_lb15_mono
  change QuotientRankAtLeast (spanCodes [272, 84, 32, 10, 1]) 15 at h
  exact bind_exact
    [272, 84, 32, 10, 1] [272, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep183 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 183))
      (frozenWangTable.lower 183) := by
  rw [show frozenWangTable.basis 183 = [384, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 183 = 15 by decide]
  have h := QiushiMatmul.plane298GenBound0004
  change QuotientRankAtLeast (spanCodes [384, 84, 32, 10, 1]) 15 at h
  exact bind_exact
    [384, 84, 32, 10, 1] [384, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep184 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 184))
      (frozenWangTable.lower 184) := by
  rw [show frozenWangTable.basis 184 = [386, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 184 = 15 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound184
  change QuotientRankAtLeast (spanCodes [386, 84, 32, 10, 1]) 15 at h
  exact bind_exact
    [386, 84, 32, 10, 1] [386, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep185 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 185))
      (frozenWangTable.lower 185) := by
  rw [show frozenWangTable.basis 185 = [400, 84, 32, 10, 1] by decide,
      show frozenWangTable.lower 185 = 15 by decide]
  have h := QiushiMatmul.step109_orbit185_lb15_wc
  change QuotientRankAtLeast (spanCodes [400, 84, 32, 10, 1]) 15 at h
  exact bind_exact
    [400, 84, 32, 10, 1] [400, 84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep186 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 186))
      (frozenWangTable.lower 186) := by
  rw [show frozenWangTable.basis 186 = [258, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 186 = 15 by decide]
  have h := QiushiMatmul.orbit186_lb15_mono
  change QuotientRankAtLeast (spanCodes [258, 128, 32, 10, 1]) 15 at h
  exact bind_exact
    [258, 128, 32, 10, 1] [258, 128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep187 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 187))
      (frozenWangTable.lower 187) := by
  rw [show frozenWangTable.basis 187 = [262, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 187 = 15 by decide]
  have h := QiushiMatmul.plane292GenBound0009
  change QuotientRankAtLeast (spanCodes [262, 128, 32, 10, 1]) 15 at h
  exact bind_exact
    [262, 128, 32, 10, 1] [262, 128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep188 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 188))
      (frozenWangTable.lower 188) := by
  rw [show frozenWangTable.basis 188 = [274, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 188 = 15 by decide]
  have h := QiushiMatmul.orbit188_lb15_mono
  change QuotientRankAtLeast (spanCodes [274, 128, 32, 10, 1]) 15 at h
  exact bind_exact
    [274, 128, 32, 10, 1] [274, 128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep189 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 189))
      (frozenWangTable.lower 189) := by
  rw [show frozenWangTable.basis 189 = [278, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 189 = 15 by decide]
  have h := QiushiMatmul.orbit189_lb15_mono
  change QuotientRankAtLeast (spanCodes [278, 128, 32, 10, 1]) 15 at h
  exact bind_exact
    [278, 128, 32, 10, 1] [278, 128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep190 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 190))
      (frozenWangTable.lower 190) := by
  rw [show frozenWangTable.basis 190 = [324, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 190 = 15 by decide]
  have h := QiushiMatmul.orbit190_lb15_mono
  change QuotientRankAtLeast (spanCodes [324, 128, 32, 10, 1]) 15 at h
  exact bind_exact
    [324, 128, 32, 10, 1] [324, 128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep191 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 191))
      (frozenWangTable.lower 191) := by
  rw [show frozenWangTable.basis 191 = [326, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 191 = 14 by decide]
  have h := QiushiMatmul.step109wc179s3Dispatch
  change QuotientRankAtLeast (spanCodes [274, 128, 84, 32, 10, 1]) 14 at h
  exact bind_contained
    [326, 128, 32, 10, 1] [274, 128, 84, 32, 10, 1] h
    (by decide) (by decide)

theorem rep192 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 192))
      (frozenWangTable.lower 192) := by
  rw [show frozenWangTable.basis 192 = [340, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 192 = 15 by decide]
  have h := QiushiMatmul.orbit192_lb15_mono
  change QuotientRankAtLeast (spanCodes [340, 128, 32, 10, 1]) 15 at h
  exact bind_exact
    [340, 128, 32, 10, 1] [340, 128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep193 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 193))
      (frozenWangTable.lower 193) := by
  rw [show frozenWangTable.basis 193 = [342, 128, 32, 10, 1] by decide,
      show frozenWangTable.lower 193 = 15 by decide]
  have h := QiushiMatmul.orbit193_lb15_mono
  change QuotientRankAtLeast (spanCodes [342, 128, 32, 10, 1]) 15 at h
  exact bind_exact
    [342, 128, 32, 10, 1] [342, 128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep194 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 194))
      (frozenWangTable.lower 194) := by
  rw [show frozenWangTable.basis 194 = [262, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 194 = 16 by decide]
  have h := QiushiMatmul.step109_orbit194_lb16_wc
  change QuotientRankAtLeast (spanCodes [262, 132, 32, 10, 1]) 16 at h
  exact bind_exact
    [262, 132, 32, 10, 1] [262, 132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep195 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 195))
      (frozenWangTable.lower 195) := by
  rw [show frozenWangTable.basis 195 = [274, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 195 = 15 by decide]
  have h := QiushiMatmul.orbit195_lb15_mono
  change QuotientRankAtLeast (spanCodes [274, 132, 32, 10, 1]) 15 at h
  exact bind_exact
    [274, 132, 32, 10, 1] [274, 132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep196 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 196))
      (frozenWangTable.lower 196) := by
  rw [show frozenWangTable.basis 196 = [278, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 196 = 16 by decide]
  have h := QiushiMatmul.step99_orbit196_lb16_unconditional
  change QuotientRankAtLeast (spanCodes [278, 132, 32, 10, 1]) 16 at h
  exact bind_exact
    [278, 132, 32, 10, 1] [278, 132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep197 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 197))
      (frozenWangTable.lower 197) := by
  rw [show frozenWangTable.basis 197 = [324, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 197 = 15 by decide]
  have h := QiushiMatmul.step109_orbit197_lb15_wc
  change QuotientRankAtLeast (spanCodes [324, 132, 32, 10, 1]) 15 at h
  exact bind_exact
    [324, 132, 32, 10, 1] [324, 132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep198 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 198))
      (frozenWangTable.lower 198) := by
  rw [show frozenWangTable.basis 198 = [326, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 198 = 15 by decide]
  have h := QiushiMatmul.orbit198_lb15_mono
  change QuotientRankAtLeast (spanCodes [326, 132, 32, 10, 1]) 15 at h
  exact bind_exact
    [326, 132, 32, 10, 1] [326, 132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep199 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 199))
      (frozenWangTable.lower 199) := by
  rw [show frozenWangTable.basis 199 = [336, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 199 = 15 by decide]
  have h := QiushiMatmul.orbit199_lb15_mono
  change QuotientRankAtLeast (spanCodes [336, 132, 32, 10, 1]) 15 at h
  exact bind_exact
    [336, 132, 32, 10, 1] [336, 132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep200 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 200))
      (frozenWangTable.lower 200) := by
  rw [show frozenWangTable.basis 200 = [338, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 200 = 15 by decide]
  exact Transport.bound200

theorem rep201 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 201))
      (frozenWangTable.lower 201) := by
  rw [show frozenWangTable.basis 201 = [340, 132, 32, 10, 1] by decide,
      show frozenWangTable.lower 201 = 16 by decide]
  have h := QiushiMatmul.step109_orbit201_lb16_wc
  change QuotientRankAtLeast (spanCodes [340, 132, 32, 10, 1]) 16 at h
  exact bind_exact
    [340, 132, 32, 10, 1] [340, 132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep202 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 202))
      (frozenWangTable.lower 202) := by
  rw [show frozenWangTable.basis 202 = [304, 160, 68, 10, 1] by decide,
      show frozenWangTable.lower 202 = 16 by decide]
  have h := QiushiMatmul.step109_orbit202_lb16_wc
  change QuotientRankAtLeast (spanCodes [304, 160, 68, 10, 1]) 16 at h
  exact bind_exact
    [304, 160, 68, 10, 1] [304, 160, 68, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep203 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 203))
      (frozenWangTable.lower 203) := by
  rw [show frozenWangTable.basis 203 = [272, 176, 68, 10, 1] by decide,
      show frozenWangTable.lower 203 = 16 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound203
  change QuotientRankAtLeast (spanCodes [272, 176, 68, 10, 1]) 16 at h
  exact bind_exact
    [272, 176, 68, 10, 1] [272, 176, 68, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep204 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 204))
      (frozenWangTable.lower 204) := by
  rw [show frozenWangTable.basis 204 = [274, 176, 68, 10, 1] by decide,
      show frozenWangTable.lower 204 = 16 by decide]
  have h := QiushiMatmul.step109_orbit204_lb16_wc
  change QuotientRankAtLeast (spanCodes [274, 176, 68, 10, 1]) 16 at h
  exact bind_exact
    [274, 176, 68, 10, 1] [274, 176, 68, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep205 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 205))
      (frozenWangTable.lower 205) := by
  rw [show frozenWangTable.basis 205 = [276, 176, 68, 10, 1] by decide,
      show frozenWangTable.lower 205 = 16 by decide]
  exact Transport.bound205

theorem rep206 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 206))
      (frozenWangTable.lower 206) := by
  rw [show frozenWangTable.basis 206 = [256, 160, 84, 10, 1] by decide,
      show frozenWangTable.lower 206 = 14 by decide]
  have h := QiushiMatmul.step109wc147s8Dispatch
  change QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 10, 1]) 14 at h
  exact bind_contained
    [256, 160, 84, 10, 1] [256, 160, 68, 16, 10, 1] h
    (by decide) (by decide)

theorem rep207 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 207))
      (frozenWangTable.lower 207) := by
  rw [show frozenWangTable.basis 207 = [258, 160, 84, 10, 1] by decide,
      show frozenWangTable.lower 207 = 15 by decide]
  have h := QiushiMatmul.step109wc204s0Dispatch
  change QuotientRankAtLeast (spanCodes [258, 160, 68, 16, 10, 1]) 15 at h
  exact bind_contained
    [258, 160, 84, 10, 1] [258, 160, 68, 16, 10, 1] h
    (by decide) (by decide)

theorem rep208 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 208))
      (frozenWangTable.lower 208) := by
  rw [show frozenWangTable.basis 208 = [260, 160, 84, 10, 1] by decide,
      show frozenWangTable.lower 208 = 15 by decide]
  have h := QiushiMatmul.plane315GenBound0009
  change QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 10, 1]) 15 at h
  exact bind_contained
    [260, 160, 84, 10, 1] [260, 160, 68, 16, 10, 1] h
    (by decide) (by decide)

theorem rep209 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 209))
      (frozenWangTable.lower 209) := by
  rw [show frozenWangTable.basis 209 = [288, 160, 84, 10, 1] by decide,
      show frozenWangTable.lower 209 = 15 by decide]
  have h := QiushiMatmul.orbit209_lb15_mono
  change QuotientRankAtLeast (spanCodes [288, 160, 84, 10, 1]) 15 at h
  exact bind_exact
    [288, 160, 84, 10, 1] [288, 160, 84, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep210 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 210))
      (frozenWangTable.lower 210) := by
  rw [show frozenWangTable.basis 210 = [290, 160, 84, 10, 1] by decide,
      show frozenWangTable.lower 210 = 15 by decide]
  have h := QiushiMatmul.step103_o279_row8_qr
  change QuotientRankAtLeast (spanCodes [290, 160, 68, 16, 10, 1]) 15 at h
  exact bind_contained
    [290, 160, 84, 10, 1] [290, 160, 68, 16, 10, 1] h
    (by decide) (by decide)

theorem rep211 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 211))
      (frozenWangTable.lower 211) := by
  rw [show frozenWangTable.basis 211 = [292, 160, 84, 10, 1] by decide,
      show frozenWangTable.lower 211 = 15 by decide]
  have h := QiushiMatmul.plane487GenBound0281
  change QuotientRankAtLeast (spanCodes [292, 160, 70, 18, 10, 1]) 15 at h
  exact bind_contained
    [292, 160, 84, 10, 1] [292, 160, 70, 18, 10, 1] h
    (by decide) (by decide)

theorem rep212 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 212))
      (frozenWangTable.lower 212) := by
  rw [show frozenWangTable.basis 212 = [274, 132, 96, 10, 1] by decide,
      show frozenWangTable.lower 212 = 16 by decide]
  have h := QiushiMatmul.step109_orbit212_lb16_wc
  change QuotientRankAtLeast (spanCodes [274, 132, 96, 10, 1]) 16 at h
  exact bind_exact
    [274, 132, 96, 10, 1] [274, 132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep213 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 213))
      (frozenWangTable.lower 213) := by
  rw [show frozenWangTable.basis 213 = [276, 132, 96, 10, 1] by decide,
      show frozenWangTable.lower 213 = 16 by decide]
  have h := QiushiMatmul.step109_orbit213_lb16_wc
  change QuotientRankAtLeast (spanCodes [276, 132, 96, 10, 1]) 16 at h
  exact bind_exact
    [276, 132, 96, 10, 1] [276, 132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep214 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 214))
      (frozenWangTable.lower 214) := by
  rw [show frozenWangTable.basis 214 = [278, 132, 96, 10, 1] by decide,
      show frozenWangTable.lower 214 = 16 by decide]
  have h := QiushiMatmul.step109_orbit214_lb16_wc
  change QuotientRankAtLeast (spanCodes [278, 132, 96, 10, 1]) 16 at h
  exact bind_exact
    [278, 132, 96, 10, 1] [278, 132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep215 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 215))
      (frozenWangTable.lower 215) := by
  rw [show frozenWangTable.basis 215 = [292, 132, 96, 10, 1] by decide,
      show frozenWangTable.lower 215 = 14 by decide]
  have h := QiushiMatmul.orbit215_lb14_mono
  change QuotientRankAtLeast (spanCodes [292, 132, 96, 10, 1]) 14 at h
  exact bind_exact
    [292, 132, 96, 10, 1] [292, 132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep216 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 216))
      (frozenWangTable.lower 216) := by
  rw [show frozenWangTable.basis 216 = [294, 132, 96, 10, 1] by decide,
      show frozenWangTable.lower 216 = 16 by decide]
  have h := QiushiMatmul.step109_orbit216_lb16_wc
  change QuotientRankAtLeast (spanCodes [294, 132, 96, 10, 1]) 16 at h
  exact bind_exact
    [294, 132, 96, 10, 1] [294, 132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep217 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 217))
      (frozenWangTable.lower 217) := by
  rw [show frozenWangTable.basis 217 = [308, 132, 96, 10, 1] by decide,
      show frozenWangTable.lower 217 = 16 by decide]
  have h := QiushiMatmul.step99_orbit217_lb16_unconditional
  change QuotientRankAtLeast (spanCodes [308, 132, 96, 10, 1]) 16 at h
  exact bind_exact
    [308, 132, 96, 10, 1] [308, 132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep218 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 218))
      (frozenWangTable.lower 218) := by
  rw [show frozenWangTable.basis 218 = [310, 132, 96, 10, 1] by decide,
      show frozenWangTable.lower 218 = 16 by decide]
  have h := QiushiMatmul.step109_orbit218_lb16_wc
  change QuotientRankAtLeast (spanCodes [310, 132, 96, 10, 1]) 16 at h
  exact bind_exact
    [310, 132, 96, 10, 1] [310, 132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep219 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 219))
      (frozenWangTable.lower 219) := by
  rw [show frozenWangTable.basis 219 = [324, 192, 36, 16, 1] by decide,
      show frozenWangTable.lower 219 = 12 by decide]
  have h := QiushiMatmul.plane434GenBound0052
  change QuotientRankAtLeast (spanCodes [266, 136, 72, 34, 16, 6, 1]) 12 at h
  exact bind_contained
    [324, 192, 36, 16, 1] [266, 136, 72, 34, 16, 6, 1] h
    (by decide) (by decide)

theorem rep220 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 220))
      (frozenWangTable.lower 220) := by
  rw [show frozenWangTable.basis 220 = [334, 192, 36, 16, 1] by decide,
      show frozenWangTable.lower 220 = 15 by decide]
  have h := QiushiMatmul.plane427GenBound0061
  change QuotientRankAtLeast (spanCodes [334, 192, 36, 16, 1]) 15 at h
  exact bind_exact
    [334, 192, 36, 16, 1] [334, 192, 36, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep221 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 221))
      (frozenWangTable.lower 221) := by
  rw [show frozenWangTable.basis 221 = [330, 196, 36, 16, 1] by decide,
      show frozenWangTable.lower 221 = 15 by decide]
  have h := QiushiMatmul.orbit221_lb15_mono
  change QuotientRankAtLeast (spanCodes [330, 196, 36, 16, 1]) 15 at h
  exact bind_exact
    [330, 196, 36, 16, 1] [330, 196, 36, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep222 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 222))
      (frozenWangTable.lower 222) := by
  rw [show frozenWangTable.basis 222 = [262, 132, 96, 16, 1] by decide,
      show frozenWangTable.lower 222 = 15 by decide]
  exact Transport.bound222

theorem rep223 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 223))
      (frozenWangTable.lower 223) := by
  rw [show frozenWangTable.basis 223 = [294, 132, 96, 16, 1] by decide,
      show frozenWangTable.lower 223 = 15 by decide]
  have h := QiushiMatmul.step109wc216s0Dispatch
  change QuotientRankAtLeast (spanCodes [294, 132, 96, 16, 10, 1]) 15 at h
  exact bind_contained
    [294, 132, 96, 16, 1] [294, 132, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep224 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 224))
      (frozenWangTable.lower 224) := by
  rw [show frozenWangTable.basis 224 = [302, 132, 96, 16, 1] by decide,
      show frozenWangTable.lower 224 = 15 by decide]
  have h := QiushiMatmul.plane224BtpGen_lb15
  change QuotientRankAtLeast (spanCodes [302, 132, 96, 16, 1]) 15 at h
  exact bind_exact
    [302, 132, 96, 16, 1] [302, 132, 96, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep225 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 225))
      (frozenWangTable.lower 225) := by
  rw [show frozenWangTable.basis 225 = [262, 140, 96, 16, 1] by decide,
      show frozenWangTable.lower 225 = 15 by decide]
  have h := QiushiMatmul.plane428GenBound0029
  change QuotientRankAtLeast (spanCodes [262, 134, 96, 16, 10, 1]) 15 at h
  exact bind_contained
    [262, 140, 96, 16, 1] [262, 134, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep226 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 226))
      (frozenWangTable.lower 226) := by
  rw [show frozenWangTable.basis 226 = [290, 140, 96, 16, 1] by decide,
      show frozenWangTable.lower 226 = 15 by decide]
  exact Transport.bound226

theorem rep227 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 227))
      (frozenWangTable.lower 227) := by
  rw [show frozenWangTable.basis 227 = [294, 140, 96, 16, 1] by decide,
      show frozenWangTable.lower 227 = 15 by decide]
  have h := QiushiMatmul.plane227BtpGen_lb15
  change QuotientRankAtLeast (spanCodes [294, 140, 96, 16, 1]) 15 at h
  exact bind_exact
    [294, 140, 96, 16, 1] [294, 140, 96, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep228 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 228))
      (frozenWangTable.lower 228) := by
  rw [show frozenWangTable.basis 228 = [262, 164, 96, 16, 1] by decide,
      show frozenWangTable.lower 228 = 15 by decide]
  have h := QiushiMatmul.plane152GenBound0002
  change QuotientRankAtLeast (spanCodes [262, 164, 96, 16, 10, 1]) 15 at h
  exact bind_contained
    [262, 164, 96, 16, 1] [262, 164, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep229 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 229))
      (frozenWangTable.lower 229) := by
  rw [show frozenWangTable.basis 229 = [266, 164, 96, 16, 1] by decide,
      show frozenWangTable.lower 229 = 15 by decide]
  have h := QiushiMatmul.plane152GenBound0001
  change QuotientRankAtLeast (spanCodes [256, 164, 96, 16, 10, 1]) 15 at h
  exact bind_contained
    [266, 164, 96, 16, 1] [256, 164, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep230 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 230))
      (frozenWangTable.lower 230) := by
  rw [show frozenWangTable.basis 230 = [270, 164, 96, 16, 1] by decide,
      show frozenWangTable.lower 230 = 15 by decide]
  exact Transport.bound230

theorem rep231 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 231))
      (frozenWangTable.lower 231) := by
  rw [show frozenWangTable.basis 231 = [256, 140, 98, 16, 1] by decide,
      show frozenWangTable.lower 231 = 15 by decide]
  have h := QiushiMatmul.plane336GenBound0006
  change QuotientRankAtLeast (spanCodes [256, 140, 98, 16, 1]) 15 at h
  exact bind_exact
    [256, 140, 98, 16, 1] [256, 140, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep232 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 232))
      (frozenWangTable.lower 232) := by
  rw [show frozenWangTable.basis 232 = [258, 140, 98, 16, 1] by decide,
      show frozenWangTable.lower 232 = 15 by decide]
  have h := QiushiMatmul.orbit232_lb15_mono
  change QuotientRankAtLeast (spanCodes [258, 140, 98, 16, 1]) 15 at h
  exact bind_exact
    [258, 140, 98, 16, 1] [258, 140, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep233 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 233))
      (frozenWangTable.lower 233) := by
  rw [show frozenWangTable.basis 233 = [260, 140, 98, 16, 1] by decide,
      show frozenWangTable.lower 233 = 15 by decide]
  have h := QiushiMatmul.step109wc334s13Dispatch
  change QuotientRankAtLeast (spanCodes [260, 140, 98, 16, 1]) 15 at h
  exact bind_exact
    [260, 140, 98, 16, 1] [260, 140, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep234 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 234))
      (frozenWangTable.lower 234) := by
  rw [show frozenWangTable.basis 234 = [264, 164, 98, 16, 1] by decide,
      show frozenWangTable.lower 234 = 15 by decide]
  have h := QiushiMatmul.plane282GenSource0012
  change QuotientRankAtLeast (spanCodes [258, 164, 98, 16, 10, 1]) 15 at h
  exact bind_contained
    [264, 164, 98, 16, 1] [258, 164, 98, 16, 10, 1] h
    (by decide) (by decide)

theorem rep235 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 235))
      (frozenWangTable.lower 235) := by
  rw [show frozenWangTable.basis 235 = [326, 136, 38, 20, 1] by decide,
      show frozenWangTable.lower 235 = 16 by decide]
  have h := QiushiMatmul.step109_orbit235_lb16_wc
  change QuotientRankAtLeast (spanCodes [326, 136, 38, 20, 1]) 16 at h
  exact bind_exact
    [326, 136, 38, 20, 1] [326, 136, 38, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep236 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 236))
      (frozenWangTable.lower 236) := by
  rw [show frozenWangTable.basis 236 = [262, 136, 96, 20, 1] by decide,
      show frozenWangTable.lower 236 = 16 by decide]
  have h := QiushiMatmul.step109_orbit236_lb16_wc
  change QuotientRankAtLeast (spanCodes [262, 136, 96, 20, 1]) 16 at h
  exact bind_exact
    [262, 136, 96, 20, 1] [262, 136, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep237 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 237))
      (frozenWangTable.lower 237) := by
  rw [show frozenWangTable.basis 237 = [266, 136, 96, 20, 1] by decide,
      show frozenWangTable.lower 237 = 16 by decide]
  have h := QiushiMatmul.step99_orbit237_lb16_unconditional
  change QuotientRankAtLeast (spanCodes [266, 136, 96, 20, 1]) 16 at h
  exact bind_exact
    [266, 136, 96, 20, 1] [266, 136, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep238 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 238))
      (frozenWangTable.lower 238) := by
  rw [show frozenWangTable.basis 238 = [294, 136, 96, 20, 1] by decide,
      show frozenWangTable.lower 238 = 16 by decide]
  have h := QiushiMatmul.step109_orbit238_lb16_wc
  change QuotientRankAtLeast (spanCodes [294, 136, 96, 20, 1]) 16 at h
  exact bind_exact
    [294, 136, 96, 20, 1] [294, 136, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep239 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 239))
      (frozenWangTable.lower 239) := by
  rw [show frozenWangTable.basis 239 = [262, 160, 68, 19, 10] by decide,
      show frozenWangTable.lower 239 = 16 by decide]
  have h := QiushiMatmul.step109_orbit239_lb16_wc
  change QuotientRankAtLeast (spanCodes [262, 160, 68, 19, 10]) 16 at h
  exact bind_exact
    [262, 160, 68, 19, 10] [262, 160, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep240 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 240))
      (frozenWangTable.lower 240) := by
  rw [show frozenWangTable.basis 240 = [261, 161, 68, 19, 10] by decide,
      show frozenWangTable.lower 240 = 16 by decide]
  have h := QiushiMatmul.plane240UnusedGen_lb16
  change QuotientRankAtLeast (spanCodes [261, 161, 68, 19, 10]) 16 at h
  exact bind_exact
    [261, 161, 68, 19, 10] [261, 161, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep241 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 241))
      (frozenWangTable.lower 241) := by
  rw [show frozenWangTable.basis 241 = [258, 162, 68, 19, 10] by decide,
      show frozenWangTable.lower 241 = 16 by decide]
  have h := QiushiMatmul.step109_orbit241_lb16_wc
  change QuotientRankAtLeast (spanCodes [258, 162, 68, 19, 10]) 16 at h
  exact bind_exact
    [258, 162, 68, 19, 10] [258, 162, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep242 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 242))
      (frozenWangTable.lower 242) := by
  rw [show frozenWangTable.basis 242 = [258, 164, 68, 19, 10] by decide,
      show frozenWangTable.lower 242 = 16 by decide]
  have h := QiushiMatmul.step109_orbit242_lb16_wc
  change QuotientRankAtLeast (spanCodes [258, 164, 68, 19, 10]) 16 at h
  exact bind_exact
    [258, 164, 68, 19, 10] [258, 164, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep243 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 243))
      (frozenWangTable.lower 243) := by
  rw [show frozenWangTable.basis 243 = [131, 68, 35, 20, 10] by decide,
      show frozenWangTable.lower 243 = 17 by decide]
  have h := QiushiMatmul.orbit243_lb17_mono
  change QuotientRankAtLeast (spanCodes [131, 68, 35, 20, 10]) 17 at h
  exact bind_exact
    [131, 68, 35, 20, 10] [131, 68, 35, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep244 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 244))
      (frozenWangTable.lower 244) := by
  rw [show frozenWangTable.basis 244 = [133, 68, 35, 20, 10] by decide,
      show frozenWangTable.lower 244 = 16 by decide]
  have h := QiushiMatmul.orbit244_lb16_mono
  change QuotientRankAtLeast (spanCodes [133, 68, 35, 20, 10]) 16 at h
  exact bind_exact
    [133, 68, 35, 20, 10] [133, 68, 35, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep245 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 245))
      (frozenWangTable.lower 245) := by
  rw [show frozenWangTable.basis 245 = [262, 161, 68, 20, 10] by decide,
      show frozenWangTable.lower 245 = 16 by decide]
  have h := QiushiMatmul.orbit245_lb16_mono
  change QuotientRankAtLeast (spanCodes [262, 161, 68, 20, 10]) 16 at h
  exact bind_exact
    [262, 161, 68, 20, 10] [262, 161, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep246 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 246))
      (frozenWangTable.lower 246) := by
  rw [show frozenWangTable.basis 246 = [259, 162, 68, 20, 10] by decide,
      show frozenWangTable.lower 246 = 16 by decide]
  have h := QiushiMatmul.orbit246_lb16_mono
  change QuotientRankAtLeast (spanCodes [259, 162, 68, 20, 10]) 16 at h
  exact bind_exact
    [259, 162, 68, 20, 10] [259, 162, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep247 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 247))
      (frozenWangTable.lower 247) := by
  rw [show frozenWangTable.basis 247 = [259, 135, 96, 20, 10] by decide,
      show frozenWangTable.lower 247 = 17 by decide]
  have h := QiushiMatmul.orbit247_lb17_mono
  change QuotientRankAtLeast (spanCodes [259, 135, 96, 20, 10]) 17 at h
  exact bind_exact
    [259, 135, 96, 20, 10] [259, 135, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep248 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 248))
      (frozenWangTable.lower 248) := by
  rw [show frozenWangTable.basis 248 = [8, 4, 2, 1] by decide,
      show frozenWangTable.lower 248 = 14 by decide]
  have h := QiushiMatmul.plane248UnusedGen_lb14
  change QuotientRankAtLeast (spanCodes [8, 4, 2, 1]) 14 at h
  exact bind_exact
    [8, 4, 2, 1] [8, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep249 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 249))
      (frozenWangTable.lower 249) := by
  rw [show frozenWangTable.basis 249 = [80, 4, 2, 1] by decide,
      show frozenWangTable.lower 249 = 14 by decide]
  have h := QiushiMatmul.plane249UnusedGen_lb14
  change QuotientRankAtLeast (spanCodes [80, 4, 2, 1]) 14 at h
  exact bind_exact
    [80, 4, 2, 1] [80, 4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep250 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 250))
      (frozenWangTable.lower 250) := by
  rw [show frozenWangTable.basis 250 = [16, 8, 2, 1] by decide,
      show frozenWangTable.lower 250 = 15 by decide]
  have h := QiushiMatmul.orbit250_lb15_mono
  change QuotientRankAtLeast (spanCodes [16, 8, 2, 1]) 15 at h
  exact bind_exact
    [16, 8, 2, 1] [16, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep251 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 251))
      (frozenWangTable.lower 251) := by
  rw [show frozenWangTable.basis 251 = [20, 8, 2, 1] by decide,
      show frozenWangTable.lower 251 = 16 by decide]
  have h := QiushiMatmul.orbit251_lb16_mono
  change QuotientRankAtLeast (spanCodes [20, 8, 2, 1]) 16 at h
  exact bind_exact
    [20, 8, 2, 1] [20, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep252 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 252))
      (frozenWangTable.lower 252) := by
  rw [show frozenWangTable.basis 252 = [32, 8, 2, 1] by decide,
      show frozenWangTable.lower 252 = 15 by decide]
  have h := QiushiMatmul.orbit252_lb15_mono
  change QuotientRankAtLeast (spanCodes [32, 8, 2, 1]) 15 at h
  exact bind_exact
    [32, 8, 2, 1] [32, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep253 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 253))
      (frozenWangTable.lower 253) := by
  rw [show frozenWangTable.basis 253 = [68, 8, 2, 1] by decide,
      show frozenWangTable.lower 253 = 16 by decide]
  have h := QiushiMatmul.orbit253_lb16_mono
  change QuotientRankAtLeast (spanCodes [68, 8, 2, 1]) 16 at h
  exact bind_exact
    [68, 8, 2, 1] [68, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep254 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 254))
      (frozenWangTable.lower 254) := by
  rw [show frozenWangTable.basis 254 = [84, 8, 2, 1] by decide,
      show frozenWangTable.lower 254 = 16 by decide]
  have h := QiushiMatmul.plane254Gen_lb16
  change QuotientRankAtLeast (spanCodes [84, 8, 2, 1]) 16 at h
  exact bind_exact
    [84, 8, 2, 1] [84, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep255 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 255))
      (frozenWangTable.lower 255) := by
  rw [show frozenWangTable.basis 255 = [96, 8, 2, 1] by decide,
      show frozenWangTable.lower 255 = 16 by decide]
  have h := QiushiMatmul.plane255Gen_lb16
  change QuotientRankAtLeast (spanCodes [96, 8, 2, 1]) 16 at h
  exact bind_exact
    [96, 8, 2, 1] [96, 8, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep256 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 256))
      (frozenWangTable.lower 256) := by
  rw [show frozenWangTable.basis 256 = [160, 8, 2, 1] by decide,
      show frozenWangTable.lower 256 = 15 by decide]
  have h := QiushiMatmul.orbit108_lb15_mono
  change QuotientRankAtLeast (spanCodes [160, 84, 8, 2, 1]) 15 at h
  exact bind_contained
    [160, 8, 2, 1] [160, 84, 8, 2, 1] h
    (by decide) (by decide)

theorem rep257 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 257))
      (frozenWangTable.lower 257) := by
  rw [show frozenWangTable.basis 257 = [256, 8, 2, 1] by decide,
      show frozenWangTable.lower 257 = 14 by decide]
  have h := QiushiMatmul.orbit100_lb14_mono
  change QuotientRankAtLeast (spanCodes [256, 20, 8, 2, 1]) 14 at h
  exact bind_contained
    [256, 8, 2, 1] [256, 20, 8, 2, 1] h
    (by decide) (by decide)

theorem rep258 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 258))
      (frozenWangTable.lower 258) := by
  rw [show frozenWangTable.basis 258 = [272, 8, 2, 1] by decide,
      show frozenWangTable.lower 258 = 15 by decide]
  have h := QiushiMatmul.orbit112_lb15_mono
  change QuotientRankAtLeast (spanCodes [272, 96, 8, 2, 1]) 15 at h
  exact bind_contained
    [272, 8, 2, 1] [272, 96, 8, 2, 1] h
    (by decide) (by decide)

theorem rep259 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 259))
      (frozenWangTable.lower 259) := by
  rw [show frozenWangTable.basis 259 = [32, 12, 2, 1] by decide,
      show frozenWangTable.lower 259 = 15 by decide]
  have h := QiushiMatmul.orbit118_lb15_mono
  change QuotientRankAtLeast (spanCodes [132, 32, 12, 2, 1]) 15 at h
  exact bind_contained
    [32, 12, 2, 1] [132, 32, 12, 2, 1] h
    (by decide) (by decide)

theorem rep260 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 260))
      (frozenWangTable.lower 260) := by
  rw [show frozenWangTable.basis 260 = [80, 12, 2, 1] by decide,
      show frozenWangTable.lower 260 = 16 by decide]
  have h := QiushiMatmul.FrozenRank.rep260
  change QuotientRankAtLeast (spanCodes [80, 12, 2, 1]) 16 at h
  exact bind_exact
    [80, 12, 2, 1] [80, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep261 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 261))
      (frozenWangTable.lower 261) := by
  rw [show frozenWangTable.basis 261 = [96, 12, 2, 1] by decide,
      show frozenWangTable.lower 261 = 16 by decide]
  have h := QiushiMatmul.plane261BtpGen_lb16
  change QuotientRankAtLeast (spanCodes [96, 12, 2, 1]) 16 at h
  exact bind_exact
    [96, 12, 2, 1] [96, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep262 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 262))
      (frozenWangTable.lower 262) := by
  rw [show frozenWangTable.basis 262 = [132, 12, 2, 1] by decide,
      show frozenWangTable.lower 262 = 17 by decide]
  have h := QiushiMatmul.step113_orbit262_lb17
  change QuotientRankAtLeast (spanCodes [132, 12, 2, 1]) 17 at h
  exact bind_exact
    [132, 12, 2, 1] [132, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep263 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 263))
      (frozenWangTable.lower 263) := by
  rw [show frozenWangTable.basis 263 = [160, 12, 2, 1] by decide,
      show frozenWangTable.lower 263 = 16 by decide]
  have h := QiushiMatmul.plane263BtpGen_lb16
  change QuotientRankAtLeast (spanCodes [160, 12, 2, 1]) 16 at h
  exact bind_exact
    [160, 12, 2, 1] [160, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep264 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 264))
      (frozenWangTable.lower 264) := by
  rw [show frozenWangTable.basis 264 = [256, 12, 2, 1] by decide,
      show frozenWangTable.lower 264 = 16 by decide]
  have h := QiushiMatmul.step109_orbit264_lb16_wc
  change QuotientRankAtLeast (spanCodes [256, 12, 2, 1]) 16 at h
  exact bind_exact
    [256, 12, 2, 1] [256, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep265 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 265))
      (frozenWangTable.lower 265) := by
  rw [show frozenWangTable.basis 265 = [272, 12, 2, 1] by decide,
      show frozenWangTable.lower 265 = 16 by decide]
  have h := QiushiMatmul.plane265BtpGen_lb16
  change QuotientRankAtLeast (spanCodes [272, 12, 2, 1]) 16 at h
  exact bind_exact
    [272, 12, 2, 1] [272, 12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep266 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 266))
      (frozenWangTable.lower 266) := by
  rw [show frozenWangTable.basis 266 = [80, 32, 2, 1] by decide,
      show frozenWangTable.lower 266 = 15 by decide]
  have h := QiushiMatmul.orbit134_lb15_mono
  change QuotientRankAtLeast (spanCodes [156, 80, 32, 2, 1]) 15 at h
  exact bind_contained
    [80, 32, 2, 1] [156, 80, 32, 2, 1] h
    (by decide) (by decide)

theorem rep267 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 267))
      (frozenWangTable.lower 267) := by
  rw [show frozenWangTable.basis 267 = [84, 32, 2, 1] by decide,
      show frozenWangTable.lower 267 = 16 by decide]
  have h := QiushiMatmul.plane267Gen_lb16
  change QuotientRankAtLeast (spanCodes [84, 32, 2, 1]) 16 at h
  exact bind_exact
    [84, 32, 2, 1] [84, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep268 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 268))
      (frozenWangTable.lower 268) := by
  rw [show frozenWangTable.basis 268 = [256, 32, 2, 1] by decide,
      show frozenWangTable.lower 268 = 14 by decide]
  have h := QiushiMatmul.plane267GenBound0012
  change QuotientRankAtLeast (spanCodes [256, 84, 32, 2, 1]) 14 at h
  exact bind_contained
    [256, 32, 2, 1] [256, 84, 32, 2, 1] h
    (by decide) (by decide)

theorem rep269 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 269))
      (frozenWangTable.lower 269) := by
  rw [show frozenWangTable.basis 269 = [264, 32, 2, 1] by decide,
      show frozenWangTable.lower 269 = 16 by decide]
  have h := QiushiMatmul.plane269Gen_lb16
  change QuotientRankAtLeast (spanCodes [264, 32, 2, 1]) 16 at h
  exact bind_exact
    [264, 32, 2, 1] [264, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep270 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 270))
      (frozenWangTable.lower 270) := by
  rw [show frozenWangTable.basis 270 = [320, 32, 2, 1] by decide,
      show frozenWangTable.lower 270 = 15 by decide]
  have h := QiushiMatmul.plane270Gen_lb15
  change QuotientRankAtLeast (spanCodes [320, 32, 2, 1]) 15 at h
  exact bind_exact
    [320, 32, 2, 1] [320, 32, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep271 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 271))
      (frozenWangTable.lower 271) := by
  rw [show frozenWangTable.basis 271 = [336, 32, 2, 1] by decide,
      show frozenWangTable.lower 271 = 15 by decide]
  exact Transport.bound271

theorem rep272 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 272))
      (frozenWangTable.lower 272) := by
  rw [show frozenWangTable.basis 272 = [152, 80, 2, 1] by decide,
      show frozenWangTable.lower 272 = 15 by decide]
  have h := QiushiMatmul.plane486GenBound0119
  change QuotientRankAtLeast (spanCodes [132, 68, 20, 8, 2, 1]) 15 at h
  exact bind_contained
    [152, 80, 2, 1] [132, 68, 20, 8, 2, 1] h
    (by decide) (by decide)

theorem rep273 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 273))
      (frozenWangTable.lower 273) := by
  rw [show frozenWangTable.basis 273 = [156, 80, 2, 1] by decide,
      show frozenWangTable.lower 273 = 16 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound273
  change QuotientRankAtLeast (spanCodes [156, 80, 2, 1]) 16 at h
  exact bind_exact
    [156, 80, 2, 1] [156, 80, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep274 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 274))
      (frozenWangTable.lower 274) := by
  rw [show frozenWangTable.basis 274 = [160, 80, 2, 1] by decide,
      show frozenWangTable.lower 274 = 16 by decide]
  have h := QiushiMatmul.plane274Gen_lb16
  change QuotientRankAtLeast (spanCodes [160, 80, 2, 1]) 16 at h
  exact bind_exact
    [160, 80, 2, 1] [160, 80, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep275 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 275))
      (frozenWangTable.lower 275) := by
  rw [show frozenWangTable.basis 275 = [160, 84, 2, 1] by decide,
      show frozenWangTable.lower 275 = 16 by decide]
  have h := QiushiMatmul.plane275Gen_lb16
  change QuotientRankAtLeast (spanCodes [160, 84, 2, 1]) 16 at h
  exact bind_exact
    [160, 84, 2, 1] [160, 84, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep276 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 276))
      (frozenWangTable.lower 276) := by
  rw [show frozenWangTable.basis 276 = [272, 96, 2, 1] by decide,
      show frozenWangTable.lower 276 = 16 by decide]
  have h := QiushiMatmul.plane276Gen_lb16
  change QuotientRankAtLeast (spanCodes [272, 96, 2, 1]) 16 at h
  exact bind_exact
    [272, 96, 2, 1] [272, 96, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep277 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 277))
      (frozenWangTable.lower 277) := by
  rw [show frozenWangTable.basis 277 = [296, 96, 2, 1] by decide,
      show frozenWangTable.lower 277 = 15 by decide]
  exact Transport.bound277

theorem rep278 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 278))
      (frozenWangTable.lower 278) := by
  rw [show frozenWangTable.basis 278 = [304, 96, 2, 1] by decide,
      show frozenWangTable.lower 278 = 16 by decide]
  have h := QiushiMatmul.plane278Gen_lb16
  change QuotientRankAtLeast (spanCodes [304, 96, 2, 1]) 16 at h
  exact bind_exact
    [304, 96, 2, 1] [304, 96, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep279 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 279))
      (frozenWangTable.lower 279) := by
  rw [show frozenWangTable.basis 279 = [68, 16, 10, 1] by decide,
      show frozenWangTable.lower 279 = 17 by decide]
  have h := QiushiMatmul.plane487GenBound0081
  change QuotientRankAtLeast (spanCodes [68, 16, 10, 1]) 17 at h
  exact bind_exact
    [68, 16, 10, 1] [68, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep280 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 280))
      (frozenWangTable.lower 280) := by
  rw [show frozenWangTable.basis 280 = [96, 16, 10, 1] by decide,
      show frozenWangTable.lower 280 = 16 by decide]
  have h := QiushiMatmul.plane152Gen_lb16
  change QuotientRankAtLeast (spanCodes [164, 96, 16, 10, 1]) 16 at h
  exact bind_contained
    [96, 16, 10, 1] [164, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep281 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 281))
      (frozenWangTable.lower 281) := by
  rw [show frozenWangTable.basis 281 = [256, 16, 10, 1] by decide,
      show frozenWangTable.lower 281 = 16 by decide]
  have h := QiushiMatmul.plane434GenBound0000
  change QuotientRankAtLeast (spanCodes [256, 16, 10, 1]) 16 at h
  exact bind_exact
    [256, 16, 10, 1] [256, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep282 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 282))
      (frozenWangTable.lower 282) := by
  rw [show frozenWangTable.basis 282 = [258, 16, 10, 1] by decide,
      show frozenWangTable.lower 282 = 17 by decide]
  have h := QiushiMatmul.plane282Gen_lb17
  change QuotientRankAtLeast (spanCodes [258, 16, 10, 1]) 17 at h
  exact bind_exact
    [258, 16, 10, 1] [258, 16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep283 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 283))
      (frozenWangTable.lower 283) := by
  rw [show frozenWangTable.basis 283 = [32, 20, 10, 1] by decide,
      show frozenWangTable.lower 283 = 16 by decide]
  have h := QiushiMatmul.plane419GenBound0005
  change QuotientRankAtLeast (spanCodes [68, 32, 20, 10, 1]) 16 at h
  exact bind_contained
    [32, 20, 10, 1] [68, 32, 20, 10, 1] h
    (by decide) (by decide)

theorem rep284 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 284))
      (frozenWangTable.lower 284) := by
  rw [show frozenWangTable.basis 284 = [68, 20, 10, 1] by decide,
      show frozenWangTable.lower 284 = 17 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound284
  change QuotientRankAtLeast (spanCodes [68, 20, 10, 1]) 17 at h
  exact bind_exact
    [68, 20, 10, 1] [68, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep285 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 285))
      (frozenWangTable.lower 285) := by
  rw [show frozenWangTable.basis 285 = [96, 20, 10, 1] by decide,
      show frozenWangTable.lower 285 = 17 by decide]
  have h := QiushiMatmul.plane285BtpGen_lb17
  change QuotientRankAtLeast (spanCodes [96, 20, 10, 1]) 17 at h
  exact bind_exact
    [96, 20, 10, 1] [96, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep286 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 286))
      (frozenWangTable.lower 286) := by
  rw [show frozenWangTable.basis 286 = [128, 20, 10, 1] by decide,
      show frozenWangTable.lower 286 = 16 by decide]
  have h := QiushiMatmul.plane455GenBound0016
  change QuotientRankAtLeast (spanCodes [128, 68, 20, 10, 1]) 16 at h
  exact bind_contained
    [128, 20, 10, 1] [128, 68, 20, 10, 1] h
    (by decide) (by decide)

theorem rep287 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 287))
      (frozenWangTable.lower 287) := by
  rw [show frozenWangTable.basis 287 = [160, 20, 10, 1] by decide,
      show frozenWangTable.lower 287 = 17 by decide]
  have h := QiushiMatmul.plane287BtpGen_lb17
  change QuotientRankAtLeast (spanCodes [160, 20, 10, 1]) 17 at h
  exact bind_exact
    [160, 20, 10, 1] [160, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep288 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 288))
      (frozenWangTable.lower 288) := by
  rw [show frozenWangTable.basis 288 = [256, 20, 10, 1] by decide,
      show frozenWangTable.lower 288 = 16 by decide]
  have h := QiushiMatmul.orbit288_lb16_mono
  change QuotientRankAtLeast (spanCodes [256, 20, 10, 1]) 16 at h
  exact bind_exact
    [256, 20, 10, 1] [256, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep289 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 289))
      (frozenWangTable.lower 289) := by
  rw [show frozenWangTable.basis 289 = [258, 20, 10, 1] by decide,
      show frozenWangTable.lower 289 = 17 by decide]
  have h := QiushiMatmul.plane289UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [258, 20, 10, 1]) 17 at h
  exact bind_exact
    [258, 20, 10, 1] [258, 20, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep290 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 290))
      (frozenWangTable.lower 290) := by
  rw [show frozenWangTable.basis 290 = [68, 32, 10, 1] by decide,
      show frozenWangTable.lower 290 = 17 by decide]
  have h := QiushiMatmul.plane419GenBound0000
  change QuotientRankAtLeast (spanCodes [68, 32, 10, 1]) 17 at h
  exact bind_exact
    [68, 32, 10, 1] [68, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep291 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 291))
      (frozenWangTable.lower 291) := by
  rw [show frozenWangTable.basis 291 = [84, 32, 10, 1] by decide,
      show frozenWangTable.lower 291 = 16 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound291
  change QuotientRankAtLeast (spanCodes [84, 32, 10, 1]) 16 at h
  exact bind_exact
    [84, 32, 10, 1] [84, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep292 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 292))
      (frozenWangTable.lower 292) := by
  rw [show frozenWangTable.basis 292 = [128, 32, 10, 1] by decide,
      show frozenWangTable.lower 292 = 16 by decide]
  have h := QiushiMatmul.plane292Gen_lb16
  change QuotientRankAtLeast (spanCodes [128, 32, 10, 1]) 16 at h
  exact bind_exact
    [128, 32, 10, 1] [128, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep293 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 293))
      (frozenWangTable.lower 293) := by
  rw [show frozenWangTable.basis 293 = [132, 32, 10, 1] by decide,
      show frozenWangTable.lower 293 = 16 by decide]
  have h := QiushiMatmul.orbit293_lb16_mono
  change QuotientRankAtLeast (spanCodes [132, 32, 10, 1]) 16 at h
  exact bind_exact
    [132, 32, 10, 1] [132, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep294 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 294))
      (frozenWangTable.lower 294) := by
  rw [show frozenWangTable.basis 294 = [258, 32, 10, 1] by decide,
      show frozenWangTable.lower 294 = 16 by decide]
  have h := QiushiMatmul.orbit294_lb16_mono
  change QuotientRankAtLeast (spanCodes [258, 32, 10, 1]) 16 at h
  exact bind_exact
    [258, 32, 10, 1] [258, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep295 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 295))
      (frozenWangTable.lower 295) := by
  rw [show frozenWangTable.basis 295 = [272, 32, 10, 1] by decide,
      show frozenWangTable.lower 295 = 17 by decide]
  have h := QiushiMatmul.plane295Gen_lb17
  change QuotientRankAtLeast (spanCodes [272, 32, 10, 1]) 17 at h
  exact bind_exact
    [272, 32, 10, 1] [272, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep296 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 296))
      (frozenWangTable.lower 296) := by
  rw [show frozenWangTable.basis 296 = [320, 32, 10, 1] by decide,
      show frozenWangTable.lower 296 = 16 by decide]
  have h := QiushiMatmul.plane419GenBound0022
  change QuotientRankAtLeast (spanCodes [262, 70, 32, 10, 1]) 16 at h
  exact bind_contained
    [320, 32, 10, 1] [262, 70, 32, 10, 1] h
    (by decide) (by decide)

theorem rep297 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 297))
      (frozenWangTable.lower 297) := by
  rw [show frozenWangTable.basis 297 = [336, 32, 10, 1] by decide,
      show frozenWangTable.lower 297 = 16 by decide]
  have h := QiushiMatmul.orbit297_lb16_mono
  change QuotientRankAtLeast (spanCodes [336, 32, 10, 1]) 16 at h
  exact bind_exact
    [336, 32, 10, 1] [336, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep298 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 298))
      (frozenWangTable.lower 298) := by
  rw [show frozenWangTable.basis 298 = [384, 32, 10, 1] by decide,
      show frozenWangTable.lower 298 = 16 by decide]
  have h := QiushiMatmul.plane298Gen_lb16
  change QuotientRankAtLeast (spanCodes [384, 32, 10, 1]) 16 at h
  exact bind_exact
    [384, 32, 10, 1] [384, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep299 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 299))
      (frozenWangTable.lower 299) := by
  rw [show frozenWangTable.basis 299 = [386, 32, 10, 1] by decide,
      show frozenWangTable.lower 299 = 16 by decide]
  have h := QiushiMatmul.orbit299_lb16_mono
  change QuotientRankAtLeast (spanCodes [386, 32, 10, 1]) 16 at h
  exact bind_exact
    [386, 32, 10, 1] [386, 32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep300 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 300))
      (frozenWangTable.lower 300) := by
  rw [show frozenWangTable.basis 300 = [160, 68, 10, 1] by decide,
      show frozenWangTable.lower 300 = 17 by decide]
  have h := QiushiMatmul.plane459GenBound0000
  change QuotientRankAtLeast (spanCodes [160, 68, 10, 1]) 17 at h
  exact bind_exact
    [160, 68, 10, 1] [160, 68, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep301 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 301))
      (frozenWangTable.lower 301) := by
  rw [show frozenWangTable.basis 301 = [176, 68, 10, 1] by decide,
      show frozenWangTable.lower 301 = 17 by decide]
  have h := QiushiMatmul.plane301UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [176, 68, 10, 1]) 17 at h
  exact bind_exact
    [176, 68, 10, 1] [176, 68, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep302 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 302))
      (frozenWangTable.lower 302) := by
  rw [show frozenWangTable.basis 302 = [304, 68, 10, 1] by decide,
      show frozenWangTable.lower 302 = 17 by decide]
  have h := QiushiMatmul.plane302UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [304, 68, 10, 1]) 17 at h
  exact bind_exact
    [304, 68, 10, 1] [304, 68, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep303 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 303))
      (frozenWangTable.lower 303) := by
  rw [show frozenWangTable.basis 303 = [160, 84, 10, 1] by decide,
      show frozenWangTable.lower 303 = 16 by decide]
  have h := QiushiMatmul.step109_orbit147_lb16_wc
  change QuotientRankAtLeast (spanCodes [160, 68, 16, 10, 1]) 16 at h
  exact bind_contained
    [160, 84, 10, 1] [160, 68, 16, 10, 1] h
    (by decide) (by decide)

theorem rep304 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 304))
      (frozenWangTable.lower 304) := by
  rw [show frozenWangTable.basis 304 = [256, 84, 10, 1] by decide,
      show frozenWangTable.lower 304 = 16 by decide]
  have h := QiushiMatmul.plane304UnusedGen_lb16
  change QuotientRankAtLeast (spanCodes [256, 84, 10, 1]) 16 at h
  exact bind_exact
    [256, 84, 10, 1] [256, 84, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep305 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 305))
      (frozenWangTable.lower 305) := by
  rw [show frozenWangTable.basis 305 = [258, 84, 10, 1] by decide,
      show frozenWangTable.lower 305 = 17 by decide]
  have h := QiushiMatmul.plane305UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [258, 84, 10, 1]) 17 at h
  exact bind_exact
    [258, 84, 10, 1] [258, 84, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep306 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 306))
      (frozenWangTable.lower 306) := by
  rw [show frozenWangTable.basis 306 = [132, 96, 10, 1] by decide,
      show frozenWangTable.lower 306 = 17 by decide]
  have h := QiushiMatmul.plane306UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [132, 96, 10, 1]) 17 at h
  exact bind_exact
    [132, 96, 10, 1] [132, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep307 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 307))
      (frozenWangTable.lower 307) := by
  rw [show frozenWangTable.basis 307 = [272, 96, 10, 1] by decide,
      show frozenWangTable.lower 307 = 17 by decide]
  have h := QiushiMatmul.plane307UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [272, 96, 10, 1]) 17 at h
  exact bind_exact
    [272, 96, 10, 1] [272, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep308 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 308))
      (frozenWangTable.lower 308) := by
  rw [show frozenWangTable.basis 308 = [288, 96, 10, 1] by decide,
      show frozenWangTable.lower 308 = 16 by decide]
  have h := QiushiMatmul.plane308UnusedGen_lb16
  change QuotientRankAtLeast (spanCodes [288, 96, 10, 1]) 16 at h
  exact bind_exact
    [288, 96, 10, 1] [288, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep309 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 309))
      (frozenWangTable.lower 309) := by
  rw [show frozenWangTable.basis 309 = [290, 96, 10, 1] by decide,
      show frozenWangTable.lower 309 = 17 by decide]
  have h := QiushiMatmul.plane309UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [290, 96, 10, 1]) 17 at h
  exact bind_exact
    [290, 96, 10, 1] [290, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep310 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 310))
      (frozenWangTable.lower 310) := by
  rw [show frozenWangTable.basis 310 = [304, 96, 10, 1] by decide,
      show frozenWangTable.lower 310 = 16 by decide]
  have h := QiushiMatmul.orbit310_lb16_mono
  change QuotientRankAtLeast (spanCodes [304, 96, 10, 1]) 16 at h
  exact bind_exact
    [304, 96, 10, 1] [304, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep311 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 311))
      (frozenWangTable.lower 311) := by
  rw [show frozenWangTable.basis 311 = [384, 96, 10, 1] by decide,
      show frozenWangTable.lower 311 = 16 by decide]
  have h := QiushiMatmul.orbit311_lb16_mono
  change QuotientRankAtLeast (spanCodes [384, 96, 10, 1]) 16 at h
  exact bind_exact
    [384, 96, 10, 1] [384, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep312 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 312))
      (frozenWangTable.lower 312) := by
  rw [show frozenWangTable.basis 312 = [386, 96, 10, 1] by decide,
      show frozenWangTable.lower 312 = 17 by decide]
  have h := QiushiMatmul.plane312UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [386, 96, 10, 1]) 17 at h
  exact bind_exact
    [386, 96, 10, 1] [386, 96, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep313 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 313))
      (frozenWangTable.lower 313) := by
  rw [show frozenWangTable.basis 313 = [256, 160, 10, 1] by decide,
      show frozenWangTable.lower 313 = 16 by decide]
  exact Transport.bound313

theorem rep314 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 314))
      (frozenWangTable.lower 314) := by
  rw [show frozenWangTable.basis 314 = [258, 160, 10, 1] by decide,
      show frozenWangTable.lower 314 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep314
  change QuotientRankAtLeast (spanCodes [258, 160, 10, 1]) 17 at h
  exact bind_exact
    [258, 160, 10, 1] [258, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep315 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 315))
      (frozenWangTable.lower 315) := by
  rw [show frozenWangTable.basis 315 = [260, 160, 10, 1] by decide,
      show frozenWangTable.lower 315 = 17 by decide]
  have h := QiushiMatmul.plane315Gen_lb17
  change QuotientRankAtLeast (spanCodes [260, 160, 10, 1]) 17 at h
  exact bind_exact
    [260, 160, 10, 1] [260, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep316 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 316))
      (frozenWangTable.lower 316) := by
  rw [show frozenWangTable.basis 316 = [262, 160, 10, 1] by decide,
      show frozenWangTable.lower 316 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep316
  change QuotientRankAtLeast (spanCodes [262, 160, 10, 1]) 17 at h
  exact bind_exact
    [262, 160, 10, 1] [262, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep317 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 317))
      (frozenWangTable.lower 317) := by
  rw [show frozenWangTable.basis 317 = [288, 160, 10, 1] by decide,
      show frozenWangTable.lower 317 = 15 by decide]
  have h := QiushiMatmul.orbit209_lb15_mono
  change QuotientRankAtLeast (spanCodes [288, 160, 84, 10, 1]) 15 at h
  exact bind_contained
    [288, 160, 10, 1] [288, 160, 84, 10, 1] h
    (by decide) (by decide)

theorem rep318 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 318))
      (frozenWangTable.lower 318) := by
  rw [show frozenWangTable.basis 318 = [290, 160, 10, 1] by decide,
      show frozenWangTable.lower 318 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep318
  change QuotientRankAtLeast (spanCodes [290, 160, 10, 1]) 17 at h
  exact bind_exact
    [290, 160, 10, 1] [290, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep319 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 319))
      (frozenWangTable.lower 319) := by
  rw [show frozenWangTable.basis 319 = [292, 160, 10, 1] by decide,
      show frozenWangTable.lower 319 = 16 by decide]
  have h := QiushiMatmul.orbit319_lb16_mono
  change QuotientRankAtLeast (spanCodes [292, 160, 10, 1]) 16 at h
  exact bind_exact
    [292, 160, 10, 1] [292, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep320 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 320))
      (frozenWangTable.lower 320) := by
  rw [show frozenWangTable.basis 320 = [304, 160, 10, 1] by decide,
      show frozenWangTable.lower 320 = 16 by decide]
  have h := QiushiMatmul.orbit320_lb16_mono
  change QuotientRankAtLeast (spanCodes [304, 160, 10, 1]) 16 at h
  exact bind_exact
    [304, 160, 10, 1] [304, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep321 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 321))
      (frozenWangTable.lower 321) := by
  rw [show frozenWangTable.basis 321 = [306, 160, 10, 1] by decide,
      show frozenWangTable.lower 321 = 17 by decide]
  have h := QiushiMatmul.plane321UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [306, 160, 10, 1]) 17 at h
  exact bind_exact
    [306, 160, 10, 1] [306, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep322 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 322))
      (frozenWangTable.lower 322) := by
  rw [show frozenWangTable.basis 322 = [308, 160, 10, 1] by decide,
      show frozenWangTable.lower 322 = 17 by decide]
  have h := QiushiMatmul.step109_orbit322_lb17_wc
  change QuotientRankAtLeast (spanCodes [308, 160, 10, 1]) 17 at h
  exact bind_exact
    [308, 160, 10, 1] [308, 160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep323 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 323))
      (frozenWangTable.lower 323) := by
  rw [show frozenWangTable.basis 323 = [192, 36, 16, 1] by decide,
      show frozenWangTable.lower 323 = 15 by decide]
  have h := QiushiMatmul.orbit323_lb15_mono
  change QuotientRankAtLeast (spanCodes [192, 36, 16, 1]) 15 at h
  exact bind_exact
    [192, 36, 16, 1] [192, 36, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep324 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 324))
      (frozenWangTable.lower 324) := by
  rw [show frozenWangTable.basis 324 = [196, 36, 16, 1] by decide,
      show frozenWangTable.lower 324 = 16 by decide]
  have h := QiushiMatmul.plane324Gen_lb16
  change QuotientRankAtLeast (spanCodes [196, 36, 16, 1]) 16 at h
  exact bind_exact
    [196, 36, 16, 1] [196, 36, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep325 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 325))
      (frozenWangTable.lower 325) := by
  rw [show frozenWangTable.basis 325 = [448, 36, 16, 1] by decide,
      show frozenWangTable.lower 325 = 15 by decide]
  have h := QiushiMatmul.orbit325_lb15_mono
  change QuotientRankAtLeast (spanCodes [448, 36, 16, 1]) 15 at h
  exact bind_exact
    [448, 36, 16, 1] [448, 36, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep326 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 326))
      (frozenWangTable.lower 326) := by
  rw [show frozenWangTable.basis 326 = [450, 36, 16, 1] by decide,
      show frozenWangTable.lower 326 = 15 by decide]
  have h := QiushiMatmul.plane324GenBound0008
  change QuotientRankAtLeast (spanCodes [262, 196, 36, 16, 1]) 15 at h
  exact bind_contained
    [450, 36, 16, 1] [262, 196, 36, 16, 1] h
    (by decide) (by decide)

theorem rep327 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 327))
      (frozenWangTable.lower 327) := by
  rw [show frozenWangTable.basis 327 = [132, 96, 16, 1] by decide,
      show frozenWangTable.lower 327 = 15 by decide]
  have h := QiushiMatmul.plane282GenSource0018
  change QuotientRankAtLeast (spanCodes [258, 132, 96, 16, 10, 1]) 15 at h
  exact bind_contained
    [132, 96, 16, 1] [258, 132, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep328 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 328))
      (frozenWangTable.lower 328) := by
  rw [show frozenWangTable.basis 328 = [140, 96, 16, 1] by decide,
      show frozenWangTable.lower 328 = 16 by decide]
  have h := QiushiMatmul.plane328UnusedGen_lb16
  change QuotientRankAtLeast (spanCodes [140, 96, 16, 1]) 16 at h
  exact bind_exact
    [140, 96, 16, 1] [140, 96, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep329 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 329))
      (frozenWangTable.lower 329) := by
  rw [show frozenWangTable.basis 329 = [164, 96, 16, 1] by decide,
      show frozenWangTable.lower 329 = 16 by decide]
  have h := QiushiMatmul.plane152Gen_lb16
  change QuotientRankAtLeast (spanCodes [164, 96, 16, 10, 1]) 16 at h
  exact bind_contained
    [164, 96, 16, 1] [164, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep330 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 330))
      (frozenWangTable.lower 330) := by
  rw [show frozenWangTable.basis 330 = [258, 96, 16, 1] by decide,
      show frozenWangTable.lower 330 = 16 by decide]
  have h := QiushiMatmul.plane433GenBound0010
  change QuotientRankAtLeast (spanCodes [258, 74, 42, 16, 1]) 16 at h
  exact bind_contained
    [258, 96, 16, 1] [258, 74, 42, 16, 1] h
    (by decide) (by decide)

theorem rep331 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 331))
      (frozenWangTable.lower 331) := by
  rw [show frozenWangTable.basis 331 = [290, 96, 16, 1] by decide,
      show frozenWangTable.lower 331 = 15 by decide]
  have h := QiushiMatmul.plane152GenBound0003
  change QuotientRankAtLeast (spanCodes [290, 164, 96, 16, 10, 1]) 15 at h
  exact bind_contained
    [290, 96, 16, 1] [290, 164, 96, 16, 10, 1] h
    (by decide) (by decide)

theorem rep332 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 332))
      (frozenWangTable.lower 332) := by
  rw [show frozenWangTable.basis 332 = [296, 96, 16, 1] by decide,
      show frozenWangTable.lower 332 = 16 by decide]
  have h := QiushiMatmul.plane433GenBound0010
  change QuotientRankAtLeast (spanCodes [258, 74, 42, 16, 1]) 16 at h
  exact bind_contained
    [296, 96, 16, 1] [258, 74, 42, 16, 1] h
    (by decide) (by decide)

theorem rep333 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 333))
      (frozenWangTable.lower 333) := by
  rw [show frozenWangTable.basis 333 = [298, 96, 16, 1] by decide,
      show frozenWangTable.lower 333 = 16 by decide]
  have h := QiushiMatmul.plane333UnusedGen_lb16
  change QuotientRankAtLeast (spanCodes [298, 96, 16, 1]) 16 at h
  exact bind_exact
    [298, 96, 16, 1] [298, 96, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep334 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 334))
      (frozenWangTable.lower 334) := by
  rw [show frozenWangTable.basis 334 = [140, 98, 16, 1] by decide,
      show frozenWangTable.lower 334 = 16 by decide]
  have h := QiushiMatmul.plane429GenBound0000
  change QuotientRankAtLeast (spanCodes [140, 98, 16, 1]) 16 at h
  exact bind_exact
    [140, 98, 16, 1] [140, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep335 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 335))
      (frozenWangTable.lower 335) := by
  rw [show frozenWangTable.basis 335 = [164, 98, 16, 1] by decide,
      show frozenWangTable.lower 335 = 16 by decide]
  exact Transport.bound335

theorem rep336 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 336))
      (frozenWangTable.lower 336) := by
  rw [show frozenWangTable.basis 336 = [256, 98, 16, 1] by decide,
      show frozenWangTable.lower 336 = 16 by decide]
  have h := QiushiMatmul.plane336Gen_lb16
  change QuotientRankAtLeast (spanCodes [256, 98, 16, 1]) 16 at h
  exact bind_exact
    [256, 98, 16, 1] [256, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep337 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 337))
      (frozenWangTable.lower 337) := by
  rw [show frozenWangTable.basis 337 = [258, 98, 16, 1] by decide,
      show frozenWangTable.lower 337 = 16 by decide]
  have h := QiushiMatmul.plane337UnusedGen_lb16
  change QuotientRankAtLeast (spanCodes [258, 98, 16, 1]) 16 at h
  exact bind_exact
    [258, 98, 16, 1] [258, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep338 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 338))
      (frozenWangTable.lower 338) := by
  rw [show frozenWangTable.basis 338 = [288, 98, 16, 1] by decide,
      show frozenWangTable.lower 338 = 16 by decide]
  have h := QiushiMatmul.plane338Gen_lb16
  change QuotientRankAtLeast (spanCodes [288, 98, 16, 1]) 16 at h
  exact bind_exact
    [288, 98, 16, 1] [288, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep339 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 339))
      (frozenWangTable.lower 339) := by
  rw [show frozenWangTable.basis 339 = [296, 98, 16, 1] by decide,
      show frozenWangTable.lower 339 = 16 by decide]
  have h := QiushiMatmul.plane339UnusedGen_lb16
  change QuotientRankAtLeast (spanCodes [296, 98, 16, 1]) 16 at h
  exact bind_exact
    [296, 98, 16, 1] [296, 98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep340 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 340))
      (frozenWangTable.lower 340) := by
  rw [show frozenWangTable.basis 340 = [258, 100, 16, 1] by decide,
      show frozenWangTable.lower 340 = 16 by decide]
  have h := QiushiMatmul.orbit340_lb16_mono
  change QuotientRankAtLeast (spanCodes [258, 100, 16, 1]) 16 at h
  exact bind_exact
    [258, 100, 16, 1] [258, 100, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep341 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 341))
      (frozenWangTable.lower 341) := by
  rw [show frozenWangTable.basis 341 = [290, 100, 16, 1] by decide,
      show frozenWangTable.lower 341 = 16 by decide]
  have h := QiushiMatmul.FrozenRegistry.ClosedReductions.bound341
  change QuotientRankAtLeast (spanCodes [290, 100, 16, 1]) 16 at h
  exact bind_exact
    [290, 100, 16, 1] [290, 100, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep342 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 342))
      (frozenWangTable.lower 342) := by
  rw [show frozenWangTable.basis 342 = [296, 100, 16, 1] by decide,
      show frozenWangTable.lower 342 = 16 by decide]
  have h := QiushiMatmul.orbit342_lb16_mono
  change QuotientRankAtLeast (spanCodes [296, 100, 16, 1]) 16 at h
  exact bind_exact
    [296, 100, 16, 1] [296, 100, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep343 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 343))
      (frozenWangTable.lower 343) := by
  rw [show frozenWangTable.basis 343 = [298, 100, 16, 1] by decide,
      show frozenWangTable.lower 343 = 16 by decide]
  have h := QiushiMatmul.orbit343_lb16_mono
  change QuotientRankAtLeast (spanCodes [298, 100, 16, 1]) 16 at h
  exact bind_exact
    [298, 100, 16, 1] [298, 100, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep344 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 344))
      (frozenWangTable.lower 344) := by
  rw [show frozenWangTable.basis 344 = [386, 100, 16, 1] by decide,
      show frozenWangTable.lower 344 = 16 by decide]
  have h := QiushiMatmul.orbit344_lb16_mono
  change QuotientRankAtLeast (spanCodes [386, 100, 16, 1]) 16 at h
  exact bind_exact
    [386, 100, 16, 1] [386, 100, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep345 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 345))
      (frozenWangTable.lower 345) := by
  rw [show frozenWangTable.basis 345 = [416, 100, 16, 1] by decide,
      show frozenWangTable.lower 345 = 15 by decide]
  have h := QiushiMatmul.plane426GenBound0115
  change QuotientRankAtLeast (spanCodes [256, 160, 100, 16, 10, 1]) 15 at h
  exact bind_contained
    [416, 100, 16, 1] [256, 160, 100, 16, 10, 1] h
    (by decide) (by decide)

theorem rep346 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 346))
      (frozenWangTable.lower 346) := by
  rw [show frozenWangTable.basis 346 = [424, 100, 16, 1] by decide,
      show frozenWangTable.lower 346 = 16 by decide]
  have h := QiushiMatmul.orbit346_lb16_mono
  change QuotientRankAtLeast (spanCodes [424, 100, 16, 1]) 16 at h
  exact bind_exact
    [424, 100, 16, 1] [424, 100, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep347 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 347))
      (frozenWangTable.lower 347) := by
  rw [show frozenWangTable.basis 347 = [258, 228, 16, 1] by decide,
      show frozenWangTable.lower 347 = 16 by decide]
  have h := QiushiMatmul.orbit347_lb16_mono
  change QuotientRankAtLeast (spanCodes [258, 228, 16, 1]) 16 at h
  exact bind_exact
    [258, 228, 16, 1] [258, 228, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep348 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 348))
      (frozenWangTable.lower 348) := by
  rw [show frozenWangTable.basis 348 = [262, 228, 16, 1] by decide,
      show frozenWangTable.lower 348 = 16 by decide]
  have h := QiushiMatmul.orbit348_lb16_mono
  change QuotientRankAtLeast (spanCodes [262, 228, 16, 1]) 16 at h
  exact bind_exact
    [262, 228, 16, 1] [262, 228, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep349 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 349))
      (frozenWangTable.lower 349) := by
  rw [show frozenWangTable.basis 349 = [292, 228, 16, 1] by decide,
      show frozenWangTable.lower 349 = 15 by decide]
  have h := QiushiMatmul.plane429GenBound0028
  change QuotientRankAtLeast (spanCodes [292, 134, 98, 16, 1]) 15 at h
  exact bind_contained
    [292, 228, 16, 1] [292, 134, 98, 16, 1] h
    (by decide) (by decide)

theorem rep350 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 350))
      (frozenWangTable.lower 350) := by
  rw [show frozenWangTable.basis 350 = [294, 228, 16, 1] by decide,
      show frozenWangTable.lower 350 = 16 by decide]
  have h := QiushiMatmul.orbit350_lb16_mono
  change QuotientRankAtLeast (spanCodes [294, 228, 16, 1]) 16 at h
  exact bind_exact
    [294, 228, 16, 1] [294, 228, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep351 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 351))
      (frozenWangTable.lower 351) := by
  rw [show frozenWangTable.basis 351 = [302, 228, 16, 1] by decide,
      show frozenWangTable.lower 351 = 16 by decide]
  have h := QiushiMatmul.orbit351_lb16_mono
  change QuotientRankAtLeast (spanCodes [302, 228, 16, 1]) 16 at h
  exact bind_exact
    [302, 228, 16, 1] [302, 228, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep352 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 352))
      (frozenWangTable.lower 352) := by
  rw [show frozenWangTable.basis 352 = [136, 38, 20, 1] by decide,
      show frozenWangTable.lower 352 = 16 by decide]
  have h := QiushiMatmul.orbit352_lb16_mono
  change QuotientRankAtLeast (spanCodes [136, 38, 20, 1]) 16 at h
  exact bind_exact
    [136, 38, 20, 1] [136, 38, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep353 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 353))
      (frozenWangTable.lower 353) := by
  rw [show frozenWangTable.basis 353 = [196, 38, 20, 1] by decide,
      show frozenWangTable.lower 353 = 17 by decide]
  have h := QiushiMatmul.plane353UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [196, 38, 20, 1]) 17 at h
  exact bind_exact
    [196, 38, 20, 1] [196, 38, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep354 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 354))
      (frozenWangTable.lower 354) := by
  rw [show frozenWangTable.basis 354 = [136, 96, 20, 1] by decide,
      show frozenWangTable.lower 354 = 17 by decide]
  have h := QiushiMatmul.plane354UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [136, 96, 20, 1]) 17 at h
  exact bind_exact
    [136, 96, 20, 1] [136, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep355 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 355))
      (frozenWangTable.lower 355) := by
  rw [show frozenWangTable.basis 355 = [164, 96, 20, 1] by decide,
      show frozenWangTable.lower 355 = 17 by decide]
  have h := QiushiMatmul.plane355UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [164, 96, 20, 1]) 17 at h
  exact bind_exact
    [164, 96, 20, 1] [164, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep356 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 356))
      (frozenWangTable.lower 356) := by
  rw [show frozenWangTable.basis 356 = [290, 96, 20, 1] by decide,
      show frozenWangTable.lower 356 = 17 by decide]
  have h := QiushiMatmul.plane356UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [290, 96, 20, 1]) 17 at h
  exact bind_exact
    [290, 96, 20, 1] [290, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep357 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 357))
      (frozenWangTable.lower 357) := by
  rw [show frozenWangTable.basis 357 = [298, 96, 20, 1] by decide,
      show frozenWangTable.lower 357 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep357
  change QuotientRankAtLeast (spanCodes [298, 96, 20, 1]) 17 at h
  exact bind_exact
    [298, 96, 20, 1] [298, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep358 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 358))
      (frozenWangTable.lower 358) := by
  rw [show frozenWangTable.basis 358 = [386, 96, 20, 1] by decide,
      show frozenWangTable.lower 358 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep358
  change QuotientRankAtLeast (spanCodes [386, 96, 20, 1]) 17 at h
  exact bind_exact
    [386, 96, 20, 1] [386, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep359 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 359))
      (frozenWangTable.lower 359) := by
  rw [show frozenWangTable.basis 359 = [424, 96, 20, 1] by decide,
      show frozenWangTable.lower 359 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep359
  change QuotientRankAtLeast (spanCodes [424, 96, 20, 1]) 17 at h
  exact bind_exact
    [424, 96, 20, 1] [424, 96, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep360 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 360))
      (frozenWangTable.lower 360) := by
  rw [show frozenWangTable.basis 360 = [160, 100, 20, 1] by decide,
      show frozenWangTable.lower 360 = 16 by decide]
  have h := QiushiMatmul.plane439GenBound0013
  change QuotientRankAtLeast (spanCodes [142, 74, 46, 20, 1]) 16 at h
  exact bind_contained
    [160, 100, 20, 1] [142, 74, 46, 20, 1] h
    (by decide) (by decide)

theorem rep361 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 361))
      (frozenWangTable.lower 361) := by
  rw [show frozenWangTable.basis 361 = [298, 100, 20, 1] by decide,
      show frozenWangTable.lower 361 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep361
  change QuotientRankAtLeast (spanCodes [298, 100, 20, 1]) 17 at h
  exact bind_exact
    [298, 100, 20, 1] [298, 100, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep362 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 362))
      (frozenWangTable.lower 362) := by
  rw [show frozenWangTable.basis 362 = [296, 102, 20, 1] by decide,
      show frozenWangTable.lower 362 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep362
  change QuotientRankAtLeast (spanCodes [296, 102, 20, 1]) 17 at h
  exact bind_exact
    [296, 102, 20, 1] [296, 102, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep363 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 363))
      (frozenWangTable.lower 363) := by
  rw [show frozenWangTable.basis 363 = [262, 160, 20, 1] by decide,
      show frozenWangTable.lower 363 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep363
  change QuotientRankAtLeast (spanCodes [262, 160, 20, 1]) 17 at h
  exact bind_exact
    [262, 160, 20, 1] [262, 160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep364 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 364))
      (frozenWangTable.lower 364) := by
  rw [show frozenWangTable.basis 364 = [264, 160, 20, 1] by decide,
      show frozenWangTable.lower 364 = 16 by decide]
  have h := QiushiMatmul.plane439GenBound0030
  change QuotientRankAtLeast (spanCodes [264, 160, 74, 20, 1]) 16 at h
  exact bind_contained
    [264, 160, 20, 1] [264, 160, 74, 20, 1] h
    (by decide) (by decide)

theorem rep365 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 365))
      (frozenWangTable.lower 365) := by
  rw [show frozenWangTable.basis 365 = [266, 160, 20, 1] by decide,
      show frozenWangTable.lower 365 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep365
  change QuotientRankAtLeast (spanCodes [266, 160, 20, 1]) 17 at h
  exact bind_exact
    [266, 160, 20, 1] [266, 160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep366 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 366))
      (frozenWangTable.lower 366) := by
  rw [show frozenWangTable.basis 366 = [268, 160, 20, 1] by decide,
      show frozenWangTable.lower 366 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep366
  change QuotientRankAtLeast (spanCodes [268, 160, 20, 1]) 17 at h
  exact bind_exact
    [268, 160, 20, 1] [268, 160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep367 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 367))
      (frozenWangTable.lower 367) := by
  rw [show frozenWangTable.basis 367 = [270, 160, 20, 1] by decide,
      show frozenWangTable.lower 367 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep367
  change QuotientRankAtLeast (spanCodes [270, 160, 20, 1]) 17 at h
  exact bind_exact
    [270, 160, 20, 1] [270, 160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep368 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 368))
      (frozenWangTable.lower 368) := by
  rw [show frozenWangTable.basis 368 = [322, 160, 20, 1] by decide,
      show frozenWangTable.lower 368 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep368
  change QuotientRankAtLeast (spanCodes [322, 160, 20, 1]) 17 at h
  exact bind_exact
    [322, 160, 20, 1] [322, 160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep369 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 369))
      (frozenWangTable.lower 369) := by
  rw [show frozenWangTable.basis 369 = [326, 160, 20, 1] by decide,
      show frozenWangTable.lower 369 = 17 by decide]
  have h := QiushiMatmul.FrozenRank.rep369
  change QuotientRankAtLeast (spanCodes [326, 160, 20, 1]) 17 at h
  exact bind_exact
    [326, 160, 20, 1] [326, 160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep370 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 370))
      (frozenWangTable.lower 370) := by
  rw [show frozenWangTable.basis 370 = [334, 160, 20, 1] by decide,
      show frozenWangTable.lower 370 = 16 by decide]
  have h := QiushiMatmul.orbit370_lb16_mono
  change QuotientRankAtLeast (spanCodes [334, 160, 20, 1]) 16 at h
  exact bind_exact
    [334, 160, 20, 1] [334, 160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep371 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 371))
      (frozenWangTable.lower 371) := by
  rw [show frozenWangTable.basis 371 = [290, 224, 20, 1] by decide,
      show frozenWangTable.lower 371 = 17 by decide]
  have h := QiushiMatmul.plane371UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [290, 224, 20, 1]) 17 at h
  exact bind_exact
    [290, 224, 20, 1] [290, 224, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep372 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 372))
      (frozenWangTable.lower 372) := by
  rw [show frozenWangTable.basis 372 = [298, 224, 20, 1] by decide,
      show frozenWangTable.lower 372 = 17 by decide]
  have h := QiushiMatmul.plane372UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [298, 224, 20, 1]) 17 at h
  exact bind_exact
    [298, 224, 20, 1] [298, 224, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep373 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 373))
      (frozenWangTable.lower 373) := by
  rw [show frozenWangTable.basis 373 = [300, 224, 20, 1] by decide,
      show frozenWangTable.lower 373 = 17 by decide]
  have h := QiushiMatmul.step107_orbit373_lb17
  change QuotientRankAtLeast (spanCodes [300, 224, 20, 1]) 17 at h
  exact bind_exact
    [300, 224, 20, 1] [300, 224, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep374 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 374))
      (frozenWangTable.lower 374) := by
  rw [show frozenWangTable.basis 374 = [282, 160, 84, 1] by decide,
      show frozenWangTable.lower 374 = 17 by decide]
  have h := QiushiMatmul.step109_orbit374_lb17_wc
  change QuotientRankAtLeast (spanCodes [282, 160, 84, 1]) 17 at h
  exact bind_exact
    [282, 160, 84, 1] [282, 160, 84, 1] h
    (by decide) (by decide) (by decide)

theorem rep375 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 375))
      (frozenWangTable.lower 375) := by
  rw [show frozenWangTable.basis 375 = [298, 160, 84, 1] by decide,
      show frozenWangTable.lower 375 = 16 by decide]
  have h := QiushiMatmul.orbit375_lb16_mono
  change QuotientRankAtLeast (spanCodes [298, 160, 84, 1]) 16 at h
  exact bind_exact
    [298, 160, 84, 1] [298, 160, 84, 1] h
    (by decide) (by decide) (by decide)

theorem rep376 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 376))
      (frozenWangTable.lower 376) := by
  rw [show frozenWangTable.basis 376 = [160, 68, 19, 10] by decide,
      show frozenWangTable.lower 376 = 17 by decide]
  have h := QiushiMatmul.plane376UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [160, 68, 19, 10]) 17 at h
  exact bind_exact
    [160, 68, 19, 10] [160, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep377 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 377))
      (frozenWangTable.lower 377) := by
  rw [show frozenWangTable.basis 377 = [161, 68, 19, 10] by decide,
      show frozenWangTable.lower 377 = 17 by decide]
  have h := QiushiMatmul.plane462GenBound0000
  change QuotientRankAtLeast (spanCodes [161, 68, 19, 10]) 17 at h
  exact bind_exact
    [161, 68, 19, 10] [161, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep378 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 378))
      (frozenWangTable.lower 378) := by
  rw [show frozenWangTable.basis 378 = [162, 68, 19, 10] by decide,
      show frozenWangTable.lower 378 = 17 by decide]
  have h := QiushiMatmul.plane378UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [162, 68, 19, 10]) 17 at h
  exact bind_exact
    [162, 68, 19, 10] [162, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep379 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 379))
      (frozenWangTable.lower 379) := by
  rw [show frozenWangTable.basis 379 = [164, 68, 19, 10] by decide,
      show frozenWangTable.lower 379 = 17 by decide]
  have h := QiushiMatmul.plane379UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [164, 68, 19, 10]) 17 at h
  exact bind_exact
    [164, 68, 19, 10] [164, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep380 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 380))
      (frozenWangTable.lower 380) := by
  rw [show frozenWangTable.basis 380 = [258, 68, 19, 10] by decide,
      show frozenWangTable.lower 380 = 17 by decide]
  have h := QiushiMatmul.plane380UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [258, 68, 19, 10]) 17 at h
  exact bind_exact
    [258, 68, 19, 10] [258, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep381 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 381))
      (frozenWangTable.lower 381) := by
  rw [show frozenWangTable.basis 381 = [261, 68, 19, 10] by decide,
      show frozenWangTable.lower 381 = 16 by decide]
  exact Transport.bound381

theorem rep382 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 382))
      (frozenWangTable.lower 382) := by
  rw [show frozenWangTable.basis 382 = [262, 68, 19, 10] by decide,
      show frozenWangTable.lower 382 = 17 by decide]
  have h := QiushiMatmul.plane382UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [262, 68, 19, 10]) 17 at h
  exact bind_exact
    [262, 68, 19, 10] [262, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep383 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 383))
      (frozenWangTable.lower 383) := by
  rw [show frozenWangTable.basis 383 = [289, 68, 19, 10] by decide,
      show frozenWangTable.lower 383 = 17 by decide]
  have h := QiushiMatmul.plane383UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [289, 68, 19, 10]) 17 at h
  exact bind_exact
    [289, 68, 19, 10] [289, 68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep384 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 384))
      (frozenWangTable.lower 384) := by
  rw [show frozenWangTable.basis 384 = [68, 35, 20, 10] by decide,
      show frozenWangTable.lower 384 = 17 by decide]
  have h := QiushiMatmul.orbit384_lb17_mono
  change QuotientRankAtLeast (spanCodes [68, 35, 20, 10]) 17 at h
  exact bind_exact
    [68, 35, 20, 10] [68, 35, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep385 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 385))
      (frozenWangTable.lower 385) := by
  rw [show frozenWangTable.basis 385 = [160, 68, 20, 10] by decide,
      show frozenWangTable.lower 385 = 17 by decide]
  have h := QiushiMatmul.orbit385_lb17_mono
  change QuotientRankAtLeast (spanCodes [160, 68, 20, 10]) 17 at h
  exact bind_exact
    [160, 68, 20, 10] [160, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep386 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 386))
      (frozenWangTable.lower 386) := by
  rw [show frozenWangTable.basis 386 = [161, 68, 20, 10] by decide,
      show frozenWangTable.lower 386 = 17 by decide]
  have h := QiushiMatmul.plane386UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [161, 68, 20, 10]) 17 at h
  exact bind_exact
    [161, 68, 20, 10] [161, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep387 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 387))
      (frozenWangTable.lower 387) := by
  rw [show frozenWangTable.basis 387 = [162, 68, 20, 10] by decide,
      show frozenWangTable.lower 387 = 17 by decide]
  have h := QiushiMatmul.plane387UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [162, 68, 20, 10]) 17 at h
  exact bind_exact
    [162, 68, 20, 10] [162, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep388 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 388))
      (frozenWangTable.lower 388) := by
  rw [show frozenWangTable.basis 388 = [164, 68, 20, 10] by decide,
      show frozenWangTable.lower 388 = 17 by decide]
  have h := QiushiMatmul.plane388UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [164, 68, 20, 10]) 17 at h
  exact bind_exact
    [164, 68, 20, 10] [164, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep389 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 389))
      (frozenWangTable.lower 389) := by
  rw [show frozenWangTable.basis 389 = [166, 68, 20, 10] by decide,
      show frozenWangTable.lower 389 = 17 by decide]
  have h := QiushiMatmul.plane389UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [166, 68, 20, 10]) 17 at h
  exact bind_exact
    [166, 68, 20, 10] [166, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep390 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 390))
      (frozenWangTable.lower 390) := by
  rw [show frozenWangTable.basis 390 = [167, 68, 20, 10] by decide,
      show frozenWangTable.lower 390 = 17 by decide]
  have h := QiushiMatmul.plane390UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [167, 68, 20, 10]) 17 at h
  exact bind_exact
    [167, 68, 20, 10] [167, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep391 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 391))
      (frozenWangTable.lower 391) := by
  rw [show frozenWangTable.basis 391 = [258, 68, 20, 10] by decide,
      show frozenWangTable.lower 391 = 16 by decide]
  have h := QiushiMatmul.orbit160_lb16_mono
  change QuotientRankAtLeast (spanCodes [258, 68, 20, 10, 1]) 16 at h
  exact bind_contained
    [258, 68, 20, 10] [258, 68, 20, 10, 1] h
    (by decide) (by decide)

theorem rep392 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 392))
      (frozenWangTable.lower 392) := by
  rw [show frozenWangTable.basis 392 = [259, 68, 20, 10] by decide,
      show frozenWangTable.lower 392 = 17 by decide]
  have h := QiushiMatmul.plane392UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [259, 68, 20, 10]) 17 at h
  exact bind_exact
    [259, 68, 20, 10] [259, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep393 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 393))
      (frozenWangTable.lower 393) := by
  rw [show frozenWangTable.basis 393 = [262, 68, 20, 10] by decide,
      show frozenWangTable.lower 393 = 17 by decide]
  have h := QiushiMatmul.orbit393_lb17_mono
  change QuotientRankAtLeast (spanCodes [262, 68, 20, 10]) 17 at h
  exact bind_exact
    [262, 68, 20, 10] [262, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep394 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 394))
      (frozenWangTable.lower 394) := by
  rw [show frozenWangTable.basis 394 = [289, 68, 20, 10] by decide,
      show frozenWangTable.lower 394 = 17 by decide]
  have h := QiushiMatmul.plane394UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [289, 68, 20, 10]) 17 at h
  exact bind_exact
    [289, 68, 20, 10] [289, 68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep395 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 395))
      (frozenWangTable.lower 395) := by
  rw [show frozenWangTable.basis 395 = [131, 96, 20, 10] by decide,
      show frozenWangTable.lower 395 = 17 by decide]
  have h := QiushiMatmul.plane395UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [131, 96, 20, 10]) 17 at h
  exact bind_exact
    [131, 96, 20, 10] [131, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep396 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 396))
      (frozenWangTable.lower 396) := by
  rw [show frozenWangTable.basis 396 = [133, 96, 20, 10] by decide,
      show frozenWangTable.lower 396 = 17 by decide]
  have h := QiushiMatmul.plane396UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [133, 96, 20, 10]) 17 at h
  exact bind_exact
    [133, 96, 20, 10] [133, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep397 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 397))
      (frozenWangTable.lower 397) := by
  rw [show frozenWangTable.basis 397 = [135, 96, 20, 10] by decide,
      show frozenWangTable.lower 397 = 17 by decide]
  have h := QiushiMatmul.orbit397_lb17_mono
  change QuotientRankAtLeast (spanCodes [135, 96, 20, 10]) 17 at h
  exact bind_exact
    [135, 96, 20, 10] [135, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep398 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 398))
      (frozenWangTable.lower 398) := by
  rw [show frozenWangTable.basis 398 = [161, 96, 20, 10] by decide,
      show frozenWangTable.lower 398 = 17 by decide]
  have h := QiushiMatmul.plane398UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [161, 96, 20, 10]) 17 at h
  exact bind_exact
    [161, 96, 20, 10] [161, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep399 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 399))
      (frozenWangTable.lower 399) := by
  rw [show frozenWangTable.basis 399 = [164, 96, 20, 10] by decide,
      show frozenWangTable.lower 399 = 17 by decide]
  have h := QiushiMatmul.plane399UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [164, 96, 20, 10]) 17 at h
  exact bind_exact
    [164, 96, 20, 10] [164, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep400 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 400))
      (frozenWangTable.lower 400) := by
  rw [show frozenWangTable.basis 400 = [259, 96, 20, 10] by decide,
      show frozenWangTable.lower 400 = 17 by decide]
  have h := QiushiMatmul.orbit400_lb17_mono
  change QuotientRankAtLeast (spanCodes [259, 96, 20, 10]) 17 at h
  exact bind_exact
    [259, 96, 20, 10] [259, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep401 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 401))
      (frozenWangTable.lower 401) := by
  rw [show frozenWangTable.basis 401 = [261, 96, 20, 10] by decide,
      show frozenWangTable.lower 401 = 17 by decide]
  have h := QiushiMatmul.plane401UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [261, 96, 20, 10]) 17 at h
  exact bind_exact
    [261, 96, 20, 10] [261, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep402 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 402))
      (frozenWangTable.lower 402) := by
  rw [show frozenWangTable.basis 402 = [391, 96, 20, 10] by decide,
      show frozenWangTable.lower 402 = 17 by decide]
  have h := QiushiMatmul.plane402UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [391, 96, 20, 10]) 17 at h
  exact bind_exact
    [391, 96, 20, 10] [391, 96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep403 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 403))
      (frozenWangTable.lower 403) := by
  rw [show frozenWangTable.basis 403 = [304, 161, 68, 10] by decide,
      show frozenWangTable.lower 403 = 17 by decide]
  have h := QiushiMatmul.plane403UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [304, 161, 68, 10]) 17 at h
  exact bind_exact
    [304, 161, 68, 10] [304, 161, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep404 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 404))
      (frozenWangTable.lower 404) := by
  rw [show frozenWangTable.basis 404 = [309, 162, 68, 10] by decide,
      show frozenWangTable.lower 404 = 17 by decide]
  have h := QiushiMatmul.plane404UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [309, 162, 68, 10]) 17 at h
  exact bind_exact
    [309, 162, 68, 10] [309, 162, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep405 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 405))
      (frozenWangTable.lower 405) := by
  rw [show frozenWangTable.basis 405 = [279, 178, 68, 10] by decide,
      show frozenWangTable.lower 405 = 16 by decide]
  have h := QiushiMatmul.plane462GenBound0001
  change QuotientRankAtLeast (spanCodes [262, 163, 68, 17, 10]) 16 at h
  exact bind_contained
    [279, 178, 68, 10] [262, 163, 68, 17, 10] h
    (by decide) (by decide)

theorem rep406 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 406))
      (frozenWangTable.lower 406) := by
  rw [show frozenWangTable.basis 406 = [276, 179, 68, 10] by decide,
      show frozenWangTable.lower 406 = 17 by decide]
  have h := QiushiMatmul.plane406UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [276, 179, 68, 10]) 17 at h
  exact bind_exact
    [276, 179, 68, 10] [276, 179, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep407 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 407))
      (frozenWangTable.lower 407) := by
  rw [show frozenWangTable.basis 407 = [257, 163, 84, 10] by decide,
      show frozenWangTable.lower 407 = 17 by decide]
  have h := QiushiMatmul.plane407UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [257, 163, 84, 10]) 17 at h
  exact bind_exact
    [257, 163, 84, 10] [257, 163, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep408 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 408))
      (frozenWangTable.lower 408) := by
  rw [show frozenWangTable.basis 408 = [262, 163, 84, 10] by decide,
      show frozenWangTable.lower 408 = 17 by decide]
  have h := QiushiMatmul.plane408UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [262, 163, 84, 10]) 17 at h
  exact bind_exact
    [262, 163, 84, 10] [262, 163, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep409 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 409))
      (frozenWangTable.lower 409) := by
  rw [show frozenWangTable.basis 409 = [276, 165, 96, 10] by decide,
      show frozenWangTable.lower 409 = 17 by decide]
  have h := QiushiMatmul.orbit409_lb17_mono
  change QuotientRankAtLeast (spanCodes [276, 165, 96, 10]) 17 at h
  exact bind_exact
    [276, 165, 96, 10] [276, 165, 96, 10] h
    (by decide) (by decide) (by decide)

theorem rep410 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 410))
      (frozenWangTable.lower 410) := by
  rw [show frozenWangTable.basis 410 = [4, 2, 1] by decide,
      show frozenWangTable.lower 410 = 15 by decide]
  have h := QiushiMatmul.plane410BtpGen_lb15
  change QuotientRankAtLeast (spanCodes [4, 2, 1]) 15 at h
  exact bind_exact
    [4, 2, 1] [4, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep411 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 411))
      (frozenWangTable.lower 411) := by
  rw [show frozenWangTable.basis 411 = [8, 2, 1] by decide,
      show frozenWangTable.lower 411 = 16 by decide]
  have h := QiushiMatmul.orbit251_lb16_mono
  change QuotientRankAtLeast (spanCodes [20, 8, 2, 1]) 16 at h
  exact bind_contained
    [8, 2, 1] [20, 8, 2, 1] h
    (by decide) (by decide)

theorem rep412 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 412))
      (frozenWangTable.lower 412) := by
  rw [show frozenWangTable.basis 412 = [12, 2, 1] by decide,
      show frozenWangTable.lower 412 = 17 by decide]
  have h := QiushiMatmul.orbit412_lb17_mono
  change QuotientRankAtLeast (spanCodes [12, 2, 1]) 17 at h
  exact bind_exact
    [12, 2, 1] [12, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep413 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 413))
      (frozenWangTable.lower 413) := by
  rw [show frozenWangTable.basis 413 = [32, 2, 1] by decide,
      show frozenWangTable.lower 413 = 16 by decide]
  have h := QiushiMatmul.plane267Gen_lb16
  change QuotientRankAtLeast (spanCodes [84, 32, 2, 1]) 16 at h
  exact bind_contained
    [32, 2, 1] [84, 32, 2, 1] h
    (by decide) (by decide)

theorem rep414 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 414))
      (frozenWangTable.lower 414) := by
  rw [show frozenWangTable.basis 414 = [80, 2, 1] by decide,
      show frozenWangTable.lower 414 = 17 by decide]
  have h := QiushiMatmul.plane481GenBound0005
  change QuotientRankAtLeast (spanCodes [68, 20, 2, 1]) 17 at h
  exact bind_contained
    [80, 2, 1] [68, 20, 2, 1] h
    (by decide) (by decide)

theorem rep415 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 415))
      (frozenWangTable.lower 415) := by
  rw [show frozenWangTable.basis 415 = [84, 2, 1] by decide,
      show frozenWangTable.lower 415 = 17 by decide]
  have h := QiushiMatmul.plane482GenBound0000
  change QuotientRankAtLeast (spanCodes [84, 2, 1]) 17 at h
  exact bind_exact
    [84, 2, 1] [84, 2, 1] h
    (by decide) (by decide) (by decide)

theorem rep416 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 416))
      (frozenWangTable.lower 416) := by
  rw [show frozenWangTable.basis 416 = [96, 2, 1] by decide,
      show frozenWangTable.lower 416 = 17 by decide]
  exact bound416

theorem rep417 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 417))
      (frozenWangTable.lower 417) := by
  rw [show frozenWangTable.basis 417 = [16, 10, 1] by decide,
      show frozenWangTable.lower 417 = 17 by decide]
  have h := QiushiMatmul.orbit417_lb17_mono
  change QuotientRankAtLeast (spanCodes [16, 10, 1]) 17 at h
  exact bind_exact
    [16, 10, 1] [16, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep418 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 418))
      (frozenWangTable.lower 418) := by
  rw [show frozenWangTable.basis 418 = [20, 10, 1] by decide,
      show frozenWangTable.lower 418 = 17 by decide]
  have h := QiushiMatmul.FrozenRegistry.UnusedAdapters.bound284
  change QuotientRankAtLeast (spanCodes [68, 20, 10, 1]) 17 at h
  exact bind_contained
    [20, 10, 1] [68, 20, 10, 1] h
    (by decide) (by decide)

theorem rep419 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 419))
      (frozenWangTable.lower 419) := by
  rw [show frozenWangTable.basis 419 = [32, 10, 1] by decide,
      show frozenWangTable.lower 419 = 17 by decide]
  have h := QiushiMatmul.plane419Gen_lb17
  change QuotientRankAtLeast (spanCodes [32, 10, 1]) 17 at h
  exact bind_exact
    [32, 10, 1] [32, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep420 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 420))
      (frozenWangTable.lower 420) := by
  rw [show frozenWangTable.basis 420 = [68, 10, 1] by decide,
      show frozenWangTable.lower 420 = 18 by decide]
  have h := QiushiMatmul.plane420BtpGen_lb18
  change QuotientRankAtLeast (spanCodes [68, 10, 1]) 18 at h
  exact bind_exact
    [68, 10, 1] [68, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep421 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 421))
      (frozenWangTable.lower 421) := by
  rw [show frozenWangTable.basis 421 = [84, 10, 1] by decide,
      show frozenWangTable.lower 421 = 17 by decide]
  have h := QiushiMatmul.orbit421_lb17_mono
  change QuotientRankAtLeast (spanCodes [84, 10, 1]) 17 at h
  exact bind_exact
    [84, 10, 1] [84, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep422 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 422))
      (frozenWangTable.lower 422) := by
  rw [show frozenWangTable.basis 422 = [96, 10, 1] by decide,
      show frozenWangTable.lower 422 = 17 by decide]
  have h := QiushiMatmul.plane488GenBound0097
  change QuotientRankAtLeast (spanCodes [260, 96, 10, 1]) 17 at h
  exact bind_contained
    [96, 10, 1] [260, 96, 10, 1] h
    (by decide) (by decide)

theorem rep423 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 423))
      (frozenWangTable.lower 423) := by
  rw [show frozenWangTable.basis 423 = [160, 10, 1] by decide,
      show frozenWangTable.lower 423 = 17 by decide]
  have h := QiushiMatmul.orbit423_lb17_mono
  change QuotientRankAtLeast (spanCodes [160, 10, 1]) 17 at h
  exact bind_exact
    [160, 10, 1] [160, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep424 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 424))
      (frozenWangTable.lower 424) := by
  rw [show frozenWangTable.basis 424 = [256, 10, 1] by decide,
      show frozenWangTable.lower 424 = 17 by decide]
  have h := QiushiMatmul.orbit424_lb17_mono
  change QuotientRankAtLeast (spanCodes [256, 10, 1]) 17 at h
  exact bind_exact
    [256, 10, 1] [256, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep425 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 425))
      (frozenWangTable.lower 425) := by
  rw [show frozenWangTable.basis 425 = [258, 10, 1] by decide,
      show frozenWangTable.lower 425 = 18 by decide]
  have h := QiushiMatmul.plane425Gen_lb18
  change QuotientRankAtLeast (spanCodes [258, 10, 1]) 18 at h
  exact bind_exact
    [258, 10, 1] [258, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep426 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 426))
      (frozenWangTable.lower 426) := by
  rw [show frozenWangTable.basis 426 = [272, 10, 1] by decide,
      show frozenWangTable.lower 426 = 18 by decide]
  have h := QiushiMatmul.plane426Gen_lb18
  change QuotientRankAtLeast (spanCodes [272, 10, 1]) 18 at h
  exact bind_exact
    [272, 10, 1] [272, 10, 1] h
    (by decide) (by decide) (by decide)

theorem rep427 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 427))
      (frozenWangTable.lower 427) := by
  rw [show frozenWangTable.basis 427 = [36, 16, 1] by decide,
      show frozenWangTable.lower 427 = 17 by decide]
  have h := QiushiMatmul.plane427Gen_lb17
  change QuotientRankAtLeast (spanCodes [36, 16, 1]) 17 at h
  exact bind_exact
    [36, 16, 1] [36, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep428 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 428))
      (frozenWangTable.lower 428) := by
  rw [show frozenWangTable.basis 428 = [96, 16, 1] by decide,
      show frozenWangTable.lower 428 = 17 by decide]
  have h := QiushiMatmul.plane428Gen_lb17
  change QuotientRankAtLeast (spanCodes [96, 16, 1]) 17 at h
  exact bind_exact
    [96, 16, 1] [96, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep429 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 429))
      (frozenWangTable.lower 429) := by
  rw [show frozenWangTable.basis 429 = [98, 16, 1] by decide,
      show frozenWangTable.lower 429 = 17 by decide]
  have h := QiushiMatmul.plane429Gen_lb17
  change QuotientRankAtLeast (spanCodes [98, 16, 1]) 17 at h
  exact bind_exact
    [98, 16, 1] [98, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep430 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 430))
      (frozenWangTable.lower 430) := by
  rw [show frozenWangTable.basis 430 = [100, 16, 1] by decide,
      show frozenWangTable.lower 430 = 17 by decide]
  have h := QiushiMatmul.plane430Gen_lb17
  change QuotientRankAtLeast (spanCodes [100, 16, 1]) 17 at h
  exact bind_exact
    [100, 16, 1] [100, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep431 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 431))
      (frozenWangTable.lower 431) := by
  rw [show frozenWangTable.basis 431 = [228, 16, 1] by decide,
      show frozenWangTable.lower 431 = 17 by decide]
  have h := QiushiMatmul.orbit431_lb17_mono
  change QuotientRankAtLeast (spanCodes [228, 16, 1]) 17 at h
  exact bind_exact
    [228, 16, 1] [228, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep432 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 432))
      (frozenWangTable.lower 432) := by
  rw [show frozenWangTable.basis 432 = [256, 16, 1] by decide,
      show frozenWangTable.lower 432 = 16 by decide]
  have h := QiushiMatmul.plane336Gen_lb16
  change QuotientRankAtLeast (spanCodes [256, 98, 16, 1]) 16 at h
  exact bind_contained
    [256, 16, 1] [256, 98, 16, 1] h
    (by decide) (by decide)

theorem rep433 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 433))
      (frozenWangTable.lower 433) := by
  rw [show frozenWangTable.basis 433 = [258, 16, 1] by decide,
      show frozenWangTable.lower 433 = 17 by decide]
  have h := QiushiMatmul.plane433Gen_lb17
  change QuotientRankAtLeast (spanCodes [258, 16, 1]) 17 at h
  exact bind_exact
    [258, 16, 1] [258, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep434 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 434))
      (frozenWangTable.lower 434) := by
  rw [show frozenWangTable.basis 434 = [266, 16, 1] by decide,
      show frozenWangTable.lower 434 = 17 by decide]
  have h := QiushiMatmul.plane434Gen_lb17
  change QuotientRankAtLeast (spanCodes [266, 16, 1]) 17 at h
  exact bind_exact
    [266, 16, 1] [266, 16, 1] h
    (by decide) (by decide) (by decide)

theorem rep435 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 435))
      (frozenWangTable.lower 435) := by
  rw [show frozenWangTable.basis 435 = [38, 20, 1] by decide,
      show frozenWangTable.lower 435 = 17 by decide]
  have h := QiushiMatmul.plane481GenBound0002
  change QuotientRankAtLeast (spanCodes [38, 20, 1]) 17 at h
  exact bind_exact
    [38, 20, 1] [38, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep436 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 436))
      (frozenWangTable.lower 436) := by
  rw [show frozenWangTable.basis 436 = [96, 20, 1] by decide,
      show frozenWangTable.lower 436 = 17 by decide]
  exact Transport.bound436

theorem rep437 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 437))
      (frozenWangTable.lower 437) := by
  rw [show frozenWangTable.basis 437 = [100, 20, 1] by decide,
      show frozenWangTable.lower 437 = 17 by decide]
  have h := QiushiMatmul.orbit437_lb17_mono
  change QuotientRankAtLeast (spanCodes [100, 20, 1]) 17 at h
  exact bind_exact
    [100, 20, 1] [100, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep438 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 438))
      (frozenWangTable.lower 438) := by
  rw [show frozenWangTable.basis 438 = [102, 20, 1] by decide,
      show frozenWangTable.lower 438 = 17 by decide]
  exact Transport.bound438

theorem rep439 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 439))
      (frozenWangTable.lower 439) := by
  rw [show frozenWangTable.basis 439 = [160, 20, 1] by decide,
      show frozenWangTable.lower 439 = 17 by decide]
  have h := QiushiMatmul.plane439Gen_lb17
  change QuotientRankAtLeast (spanCodes [160, 20, 1]) 17 at h
  exact bind_exact
    [160, 20, 1] [160, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep440 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 440))
      (frozenWangTable.lower 440) := by
  rw [show frozenWangTable.basis 440 = [224, 20, 1] by decide,
      show frozenWangTable.lower 440 = 17 by decide]
  have h := QiushiMatmul.orbit440_lb17_mono
  change QuotientRankAtLeast (spanCodes [224, 20, 1]) 17 at h
  exact bind_exact
    [224, 20, 1] [224, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep441 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 441))
      (frozenWangTable.lower 441) := by
  rw [show frozenWangTable.basis 441 = [258, 20, 1] by decide,
      show frozenWangTable.lower 441 = 17 by decide]
  have h := QiushiMatmul.plane289UnusedGen_lb17
  change QuotientRankAtLeast (spanCodes [258, 20, 10, 1]) 17 at h
  exact bind_contained
    [258, 20, 1] [258, 20, 10, 1] h
    (by decide) (by decide)

theorem rep442 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 442))
      (frozenWangTable.lower 442) := by
  rw [show frozenWangTable.basis 442 = [264, 20, 1] by decide,
      show frozenWangTable.lower 442 = 17 by decide]
  have h := QiushiMatmul.orbit442_lb17_mono
  change QuotientRankAtLeast (spanCodes [264, 20, 1]) 17 at h
  exact bind_exact
    [264, 20, 1] [264, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep443 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 443))
      (frozenWangTable.lower 443) := by
  rw [show frozenWangTable.basis 443 = [266, 20, 1] by decide,
      show frozenWangTable.lower 443 = 17 by decide]
  have h := QiushiMatmul.orbit443_lb17_mono
  change QuotientRankAtLeast (spanCodes [266, 20, 1]) 17 at h
  exact bind_exact
    [266, 20, 1] [266, 20, 1] h
    (by decide) (by decide) (by decide)

theorem rep444 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 444))
      (frozenWangTable.lower 444) := by
  rw [show frozenWangTable.basis 444 = [160, 84, 1] by decide,
      show frozenWangTable.lower 444 = 17 by decide]
  have h := QiushiMatmul.orbit444_lb17_mono
  change QuotientRankAtLeast (spanCodes [160, 84, 1]) 17 at h
  exact bind_exact
    [160, 84, 1] [160, 84, 1] h
    (by decide) (by decide) (by decide)

theorem rep445 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 445))
      (frozenWangTable.lower 445) := by
  rw [show frozenWangTable.basis 445 = [266, 84, 1] by decide,
      show frozenWangTable.lower 445 = 17 by decide]
  have h := QiushiMatmul.plane482GenBound0060
  change QuotientRankAtLeast (spanCodes [266, 170, 84, 1]) 17 at h
  exact bind_contained
    [266, 84, 1] [266, 170, 84, 1] h
    (by decide) (by decide)

theorem rep446 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 446))
      (frozenWangTable.lower 446) := by
  rw [show frozenWangTable.basis 446 = [304, 160, 1] by decide,
      show frozenWangTable.lower 446 = 17 by decide]
  have h := QiushiMatmul.orbit446_lb17_mono
  change QuotientRankAtLeast (spanCodes [304, 160, 1]) 17 at h
  exact bind_exact
    [304, 160, 1] [304, 160, 1] h
    (by decide) (by decide) (by decide)

theorem rep447 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 447))
      (frozenWangTable.lower 447) := by
  rw [show frozenWangTable.basis 447 = [306, 160, 1] by decide,
      show frozenWangTable.lower 447 = 17 by decide]
  have h := QiushiMatmul.plane447Gen_lb17
  change QuotientRankAtLeast (spanCodes [306, 160, 1]) 17 at h
  exact bind_exact
    [306, 160, 1] [306, 160, 1] h
    (by decide) (by decide) (by decide)

theorem rep448 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 448))
      (frozenWangTable.lower 448) := by
  rw [show frozenWangTable.basis 448 = [314, 160, 1] by decide,
      show frozenWangTable.lower 448 = 17 by decide]
  have h := QiushiMatmul.plane448Gen_lb17
  change QuotientRankAtLeast (spanCodes [314, 160, 1]) 17 at h
  exact bind_exact
    [314, 160, 1] [314, 160, 1] h
    (by decide) (by decide) (by decide)

theorem rep449 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 449))
      (frozenWangTable.lower 449) := by
  rw [show frozenWangTable.basis 449 = [316, 160, 1] by decide,
      show frozenWangTable.lower 449 = 17 by decide]
  have h := QiushiMatmul.plane449Gen_lb17
  change QuotientRankAtLeast (spanCodes [316, 160, 1]) 17 at h
  exact bind_exact
    [316, 160, 1] [316, 160, 1] h
    (by decide) (by decide) (by decide)

theorem rep450 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 450))
      (frozenWangTable.lower 450) := by
  rw [show frozenWangTable.basis 450 = [68, 19, 10] by decide,
      show frozenWangTable.lower 450 = 18 by decide]
  have h := QiushiMatmul.plane486GenBound0000
  change QuotientRankAtLeast (spanCodes [68, 19, 10]) 18 at h
  exact bind_exact
    [68, 19, 10] [68, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep451 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 451))
      (frozenWangTable.lower 451) := by
  rw [show frozenWangTable.basis 451 = [257, 19, 10] by decide,
      show frozenWangTable.lower 451 = 18 by decide]
  have h := QiushiMatmul.plane484GenBound0036
  change QuotientRankAtLeast (spanCodes [257, 19, 10]) 18 at h
  exact bind_exact
    [257, 19, 10] [257, 19, 10] h
    (by decide) (by decide) (by decide)

theorem rep452 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 452))
      (frozenWangTable.lower 452) := by
  rw [show frozenWangTable.basis 452 = [35, 20, 10] by decide,
      show frozenWangTable.lower 452 = 18 by decide]
  have h := QiushiMatmul.plane452Gen_lb18
  change QuotientRankAtLeast (spanCodes [35, 20, 10]) 18 at h
  exact bind_exact
    [35, 20, 10] [35, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep453 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 453))
      (frozenWangTable.lower 453) := by
  rw [show frozenWangTable.basis 453 = [68, 20, 10] by decide,
      show frozenWangTable.lower 453 = 18 by decide]
  have h := QiushiMatmul.plane453Gen_lb18
  change QuotientRankAtLeast (spanCodes [68, 20, 10]) 18 at h
  exact bind_exact
    [68, 20, 10] [68, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep454 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 454))
      (frozenWangTable.lower 454) := by
  rw [show frozenWangTable.basis 454 = [96, 20, 10] by decide,
      show frozenWangTable.lower 454 = 18 by decide]
  have h := QiushiMatmul.plane454Gen_lb18
  change QuotientRankAtLeast (spanCodes [96, 20, 10]) 18 at h
  exact bind_exact
    [96, 20, 10] [96, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep455 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 455))
      (frozenWangTable.lower 455) := by
  rw [show frozenWangTable.basis 455 = [129, 20, 10] by decide,
      show frozenWangTable.lower 455 = 18 by decide]
  have h := QiushiMatmul.plane455Gen_lb18
  change QuotientRankAtLeast (spanCodes [129, 20, 10]) 18 at h
  exact bind_exact
    [129, 20, 10] [129, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep456 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 456))
      (frozenWangTable.lower 456) := by
  rw [show frozenWangTable.basis 456 = [161, 20, 10] by decide,
      show frozenWangTable.lower 456 = 18 by decide]
  have h := QiushiMatmul.plane456Gen_lb18
  change QuotientRankAtLeast (spanCodes [161, 20, 10]) 18 at h
  exact bind_exact
    [161, 20, 10] [161, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep457 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 457))
      (frozenWangTable.lower 457) := by
  rw [show frozenWangTable.basis 457 = [449, 20, 10] by decide,
      show frozenWangTable.lower 457 = 18 by decide]
  have h := QiushiMatmul.plane457Gen_lb18
  change QuotientRankAtLeast (spanCodes [449, 20, 10]) 18 at h
  exact bind_exact
    [449, 20, 10] [449, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep458 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 458))
      (frozenWangTable.lower 458) := by
  rw [show frozenWangTable.basis 458 = [450, 20, 10] by decide,
      show frozenWangTable.lower 458 = 18 by decide]
  have h := QiushiMatmul.plane458Gen_lb18
  change QuotientRankAtLeast (spanCodes [450, 20, 10]) 18 at h
  exact bind_exact
    [450, 20, 10] [450, 20, 10] h
    (by decide) (by decide) (by decide)

theorem rep459 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 459))
      (frozenWangTable.lower 459) := by
  rw [show frozenWangTable.basis 459 = [160, 68, 10] by decide,
      show frozenWangTable.lower 459 = 18 by decide]
  have h := QiushiMatmul.plane459Gen_lb18
  change QuotientRankAtLeast (spanCodes [160, 68, 10]) 18 at h
  exact bind_exact
    [160, 68, 10] [160, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep460 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 460))
      (frozenWangTable.lower 460) := by
  rw [show frozenWangTable.basis 460 = [161, 68, 10] by decide,
      show frozenWangTable.lower 460 = 17 by decide]
  have h := QiushiMatmul.plane459GenBound0000
  change QuotientRankAtLeast (spanCodes [160, 68, 10, 1]) 17 at h
  exact bind_contained
    [161, 68, 10] [160, 68, 10, 1] h
    (by decide) (by decide)

theorem rep461 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 461))
      (frozenWangTable.lower 461) := by
  rw [show frozenWangTable.basis 461 = [162, 68, 10] by decide,
      show frozenWangTable.lower 461 = 18 by decide]
  have h := QiushiMatmul.plane461Gen_lb18
  change QuotientRankAtLeast (spanCodes [162, 68, 10]) 18 at h
  exact bind_exact
    [162, 68, 10] [162, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep462 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 462))
      (frozenWangTable.lower 462) := by
  rw [show frozenWangTable.basis 462 = [178, 68, 10] by decide,
      show frozenWangTable.lower 462 = 18 by decide]
  have h := QiushiMatmul.plane462Gen_lb18
  change QuotientRankAtLeast (spanCodes [178, 68, 10]) 18 at h
  exact bind_exact
    [178, 68, 10] [178, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep463 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 463))
      (frozenWangTable.lower 463) := by
  rw [show frozenWangTable.basis 463 = [179, 68, 10] by decide,
      show frozenWangTable.lower 463 = 18 by decide]
  have h := QiushiMatmul.plane463Gen_lb18
  change QuotientRankAtLeast (spanCodes [179, 68, 10]) 18 at h
  exact bind_exact
    [179, 68, 10] [179, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep464 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 464))
      (frozenWangTable.lower 464) := by
  rw [show frozenWangTable.basis 464 = [180, 68, 10] by decide,
      show frozenWangTable.lower 464 = 18 by decide]
  have h := QiushiMatmul.plane464Gen_lb18
  change QuotientRankAtLeast (spanCodes [180, 68, 10]) 18 at h
  exact bind_exact
    [180, 68, 10] [180, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep465 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 465))
      (frozenWangTable.lower 465) := by
  rw [show frozenWangTable.basis 465 = [304, 68, 10] by decide,
      show frozenWangTable.lower 465 = 18 by decide]
  have h := QiushiMatmul.plane465Gen_lb18
  change QuotientRankAtLeast (spanCodes [304, 68, 10]) 18 at h
  exact bind_exact
    [304, 68, 10] [304, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep466 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 466))
      (frozenWangTable.lower 466) := by
  rw [show frozenWangTable.basis 466 = [305, 68, 10] by decide,
      show frozenWangTable.lower 466 = 18 by decide]
  have h := QiushiMatmul.plane466Gen_lb18
  change QuotientRankAtLeast (spanCodes [305, 68, 10]) 18 at h
  exact bind_exact
    [305, 68, 10] [305, 68, 10] h
    (by decide) (by decide) (by decide)

theorem rep467 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 467))
      (frozenWangTable.lower 467) := by
  rw [show frozenWangTable.basis 467 = [163, 84, 10] by decide,
      show frozenWangTable.lower 467 = 18 by decide]
  have h := QiushiMatmul.plane467Gen_lb18
  change QuotientRankAtLeast (spanCodes [163, 84, 10]) 18 at h
  exact bind_exact
    [163, 84, 10] [163, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep468 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 468))
      (frozenWangTable.lower 468) := by
  rw [show frozenWangTable.basis 468 = [164, 84, 10] by decide,
      show frozenWangTable.lower 468 = 18 by decide]
  have h := QiushiMatmul.plane468Gen_lb18
  change QuotientRankAtLeast (spanCodes [164, 84, 10]) 18 at h
  exact bind_exact
    [164, 84, 10] [164, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep469 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 469))
      (frozenWangTable.lower 469) := by
  rw [show frozenWangTable.basis 469 = [258, 84, 10] by decide,
      show frozenWangTable.lower 469 = 18 by decide]
  have h := QiushiMatmul.plane469Gen_lb18
  change QuotientRankAtLeast (spanCodes [258, 84, 10]) 18 at h
  exact bind_exact
    [258, 84, 10] [258, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep470 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 470))
      (frozenWangTable.lower 470) := by
  rw [show frozenWangTable.basis 470 = [259, 84, 10] by decide,
      show frozenWangTable.lower 470 = 18 by decide]
  have h := QiushiMatmul.plane470Gen_lb18
  change QuotientRankAtLeast (spanCodes [259, 84, 10]) 18 at h
  exact bind_exact
    [259, 84, 10] [259, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep471 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 471))
      (frozenWangTable.lower 471) := by
  rw [show frozenWangTable.basis 471 = [289, 84, 10] by decide,
      show frozenWangTable.lower 471 = 18 by decide]
  have h := QiushiMatmul.plane471Gen_lb18
  change QuotientRankAtLeast (spanCodes [289, 84, 10]) 18 at h
  exact bind_exact
    [289, 84, 10] [289, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep472 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 472))
      (frozenWangTable.lower 472) := by
  rw [show frozenWangTable.basis 472 = [290, 84, 10] by decide,
      show frozenWangTable.lower 472 = 18 by decide]
  have h := QiushiMatmul.plane472Gen_lb18
  change QuotientRankAtLeast (spanCodes [290, 84, 10]) 18 at h
  exact bind_exact
    [290, 84, 10] [290, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep473 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 473))
      (frozenWangTable.lower 473) := by
  rw [show frozenWangTable.basis 473 = [293, 84, 10] by decide,
      show frozenWangTable.lower 473 = 18 by decide]
  have h := QiushiMatmul.plane473Gen_lb18
  change QuotientRankAtLeast (spanCodes [293, 84, 10]) 18 at h
  exact bind_exact
    [293, 84, 10] [293, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep474 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 474))
      (frozenWangTable.lower 474) := by
  rw [show frozenWangTable.basis 474 = [294, 84, 10] by decide,
      show frozenWangTable.lower 474 = 18 by decide]
  have h := QiushiMatmul.plane474Gen_lb18
  change QuotientRankAtLeast (spanCodes [294, 84, 10]) 18 at h
  exact bind_exact
    [294, 84, 10] [294, 84, 10] h
    (by decide) (by decide) (by decide)

theorem rep475 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 475))
      (frozenWangTable.lower 475) := by
  rw [show frozenWangTable.basis 475 = [165, 96, 10] by decide,
      show frozenWangTable.lower 475 = 18 by decide]
  have h := QiushiMatmul.plane475Gen_lb18
  change QuotientRankAtLeast (spanCodes [165, 96, 10]) 18 at h
  exact bind_exact
    [165, 96, 10] [165, 96, 10] h
    (by decide) (by decide) (by decide)

theorem rep476 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 476))
      (frozenWangTable.lower 476) := by
  rw [show frozenWangTable.basis 476 = [276, 96, 10] by decide,
      show frozenWangTable.lower 476 = 18 by decide]
  have h := QiushiMatmul.plane476Gen_lb18
  change QuotientRankAtLeast (spanCodes [276, 96, 10]) 18 at h
  exact bind_exact
    [276, 96, 10] [276, 96, 10] h
    (by decide) (by decide) (by decide)

theorem rep477 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 477))
      (frozenWangTable.lower 477) := by
  rw [show frozenWangTable.basis 477 = [286, 163, 84] by decide,
      show frozenWangTable.lower 477 = 18 by decide]
  have h := QiushiMatmul.plane477Gen_lb18
  change QuotientRankAtLeast (spanCodes [286, 163, 84]) 18 at h
  exact bind_exact
    [286, 163, 84] [286, 163, 84] h
    (by decide) (by decide) (by decide)

theorem rep478 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 478))
      (frozenWangTable.lower 478) := by
  rw [show frozenWangTable.basis 478 = [2, 1] by decide,
      show frozenWangTable.lower 478 = 17 by decide]
  have h := QiushiMatmul.line478_ledger
  change QuotientRankAtLeast (spanCodes [2, 1]) 17 at h
  exact bind_exact
    [2, 1] [2, 1] h
    (by decide) (by decide) (by decide)

theorem rep479 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 479))
      (frozenWangTable.lower 479) := by
  rw [show frozenWangTable.basis 479 = [10, 1] by decide,
      show frozenWangTable.lower 479 = 18 by decide]
  have h := QiushiMatmul.plane425Gen_lb18
  change QuotientRankAtLeast (spanCodes [258, 10, 1]) 18 at h
  exact bind_contained
    [10, 1] [258, 10, 1] h
    (by decide) (by decide)

theorem rep480 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 480))
      (frozenWangTable.lower 480) := by
  rw [show frozenWangTable.basis 480 = [16, 1] by decide,
      show frozenWangTable.lower 480 = 18 by decide]
  have h := QiushiMatmul.plane480Gen_lb18
  change QuotientRankAtLeast (spanCodes [16, 1]) 18 at h
  exact bind_exact
    [16, 1] [16, 1] h
    (by decide) (by decide) (by decide)

theorem rep481 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 481))
      (frozenWangTable.lower 481) := by
  rw [show frozenWangTable.basis 481 = [20, 1] by decide,
      show frozenWangTable.lower 481 = 18 by decide]
  have h := QiushiMatmul.plane481Gen_lb18
  change QuotientRankAtLeast (spanCodes [20, 1]) 18 at h
  exact bind_exact
    [20, 1] [20, 1] h
    (by decide) (by decide) (by decide)

theorem rep482 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 482))
      (frozenWangTable.lower 482) := by
  rw [show frozenWangTable.basis 482 = [84, 1] by decide,
      show frozenWangTable.lower 482 = 18 by decide]
  have h := QiushiMatmul.plane482Gen_lb18
  change QuotientRankAtLeast (spanCodes [84, 1]) 18 at h
  exact bind_exact
    [84, 1] [84, 1] h
    (by decide) (by decide) (by decide)

theorem rep483 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 483))
      (frozenWangTable.lower 483) := by
  rw [show frozenWangTable.basis 483 = [160, 1] by decide,
      show frozenWangTable.lower 483 = 18 by decide]
  have h := QiushiMatmul.plane483Gen_lb18
  change QuotientRankAtLeast (spanCodes [160, 1]) 18 at h
  exact bind_exact
    [160, 1] [160, 1] h
    (by decide) (by decide) (by decide)

theorem rep484 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 484))
      (frozenWangTable.lower 484) := by
  rw [show frozenWangTable.basis 484 = [19, 10] by decide,
      show frozenWangTable.lower 484 = 18 by decide]
  have h := QiushiMatmul.plane484Gen_lb19
  change QuotientRankAtLeast (spanCodes [19, 10]) 19 at h
  exact bind_exact
    [19, 10] [19, 10] h
    (by decide) (by decide) (by decide)

theorem rep485 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 485))
      (frozenWangTable.lower 485) := by
  rw [show frozenWangTable.basis 485 = [20, 10] by decide,
      show frozenWangTable.lower 485 = 18 by decide]
  have h := QiushiMatmul.plane485Gen_lb19
  change QuotientRankAtLeast (spanCodes [20, 10]) 19 at h
  exact bind_exact
    [20, 10] [20, 10] h
    (by decide) (by decide) (by decide)

theorem rep486 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 486))
      (frozenWangTable.lower 486) := by
  rw [show frozenWangTable.basis 486 = [68, 10] by decide,
      show frozenWangTable.lower 486 = 18 by decide]
  have h := QiushiMatmul.plane486Gen_lb19
  change QuotientRankAtLeast (spanCodes [68, 10]) 19 at h
  exact bind_exact
    [68, 10] [68, 10] h
    (by decide) (by decide) (by decide)

theorem rep487 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 487))
      (frozenWangTable.lower 487) := by
  rw [show frozenWangTable.basis 487 = [84, 10] by decide,
      show frozenWangTable.lower 487 = 18 by decide]
  have h := QiushiMatmul.plane487Gen_lb19
  change QuotientRankAtLeast (spanCodes [84, 10]) 19 at h
  exact bind_exact
    [84, 10] [84, 10] h
    (by decide) (by decide) (by decide)

theorem rep488 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 488))
      (frozenWangTable.lower 488) := by
  rw [show frozenWangTable.basis 488 = [96, 10] by decide,
      show frozenWangTable.lower 488 = 18 by decide]
  have h := QiushiMatmul.plane488Gen_lb19
  change QuotientRankAtLeast (spanCodes [96, 10]) 19 at h
  exact bind_exact
    [96, 10] [96, 10] h
    (by decide) (by decide) (by decide)

theorem rep489 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 489))
      (frozenWangTable.lower 489) := by
  rw [show frozenWangTable.basis 489 = [258, 10] by decide,
      show frozenWangTable.lower 489 = 18 by decide]
  have h := QiushiMatmul.plane489Gen_lb19
  change QuotientRankAtLeast (spanCodes [258, 10]) 19 at h
  exact bind_exact
    [258, 10] [258, 10] h
    (by decide) (by decide) (by decide)

theorem rep490 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 490))
      (frozenWangTable.lower 490) := by
  rw [show frozenWangTable.basis 490 = [275, 10] by decide,
      show frozenWangTable.lower 490 = 18 by decide]
  have h := QiushiMatmul.plane490Gen_lb19
  change QuotientRankAtLeast (spanCodes [275, 10]) 19 at h
  exact bind_exact
    [275, 10] [275, 10] h
    (by decide) (by decide) (by decide)

theorem rep491 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 491))
      (frozenWangTable.lower 491) := by
  rw [show frozenWangTable.basis 491 = [163, 84] by decide,
      show frozenWangTable.lower 491 = 18 by decide]
  have h := QiushiMatmul.plane491Gen_lb19
  change QuotientRankAtLeast (spanCodes [163, 84]) 19 at h
  exact bind_exact
    [163, 84] [163, 84] h
    (by decide) (by decide) (by decide)

theorem rep492 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 492))
      (frozenWangTable.lower 492) := by
  rw [show frozenWangTable.basis 492 = [1] by decide,
      show frozenWangTable.lower 492 = 19 by decide]
  have h := QiushiMatmul.line_rank1_ge19
  change QuotientRankAtLeast (spanCodes [1]) 19 at h
  exact bind_exact
    [1] [1] h
    (by decide) (by decide) (by decide)

theorem rep493 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 493))
      (frozenWangTable.lower 493) := by
  rw [show frozenWangTable.basis 493 = [10] by decide,
      show frozenWangTable.lower 493 = 19 by decide]
  have h := QiushiMatmul.plane484Gen_lb19
  change QuotientRankAtLeast (spanCodes [19, 10]) 19 at h
  exact bind_contained
    [10] [19, 10] h
    (by decide) (by decide)

theorem rep494 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 494))
      (frozenWangTable.lower 494) := by
  rw [show frozenWangTable.basis 494 = [84] by decide,
      show frozenWangTable.lower 494 = 19 by decide]
  have h := QiushiMatmul.plane487Gen_lb19
  change QuotientRankAtLeast (spanCodes [84, 10]) 19 at h
  exact bind_contained
    [84] [84, 10] h
    (by decide) (by decide)

theorem rep495 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 495))
      (frozenWangTable.lower 495) := by
  rw [show frozenWangTable.basis 495 = [] by decide,
      show frozenWangTable.lower 495 = 20 by decide]
  have h := QiushiMatmul.FrozenRegistry.zero_quotient_bound
  change QuotientRankAtLeast (spanCodes []) 21 at h
  exact bind_exact
    [] [] h
    (by decide) (by decide) (by decide)

def checkedIds : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495]

end QiushiMatmul.FrozenRegistry
