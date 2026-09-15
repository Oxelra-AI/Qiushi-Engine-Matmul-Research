import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit41FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0180 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 1), (68, 149), (36, 130), (16, 8), (14, 227), (1, 511)]
    (codeMat 468) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0181 :
    QuotientRankAtLeast (spanCodes [262, 130, 66, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 70), (130, 1), (66, 324), (36, 432), (16, 8), (12, 416), (1, 256)]
    (codeMat 85) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0182 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 326), (130, 3), (70, 68), (36, 432), (16, 24), (12, 416), (1, 256)]
    (codeMat 85) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0183 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 373), (132, 414), (68, 97), (36, 360), (16, 384), (12, 104), (1, 8)]
    (codeMat 143) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0184 :
    QuotientRankAtLeast (spanCodes [320, 132, 36, 16, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(320, 128), (132, 112), (36, 54), (16, 1), (12, 52), (2, 8), (1, 32)]
    (codeMat 266) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0185 :
    QuotientRankAtLeast (spanCodes [260, 130, 74, 36, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 1), (130, 2), (74, 160), (36, 9), (16, 130), (1, 432)]
    (codeMat 501) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane427GenSource0186 :
    QuotientRankAtLeast (spanCodes [256, 140, 64, 36, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(256, 1), (140, 116), (64, 8), (36, 2), (16, 384), (1, 32)]
    (codeMat 92) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane427GenSource0187 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 326), (128, 3), (70, 324), (36, 432), (16, 24), (12, 416), (1, 256)]
    (codeMat 84) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0188 :
    QuotientRankAtLeast (spanCodes [260, 134, 66, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (134, 126), (66, 245), (36, 8), (16, 384), (12, 264), (1, 360)]
    (codeMat 158) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0189 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 70), (128, 1), (66, 68), (36, 432), (16, 8), (12, 416), (1, 256)]
    (codeMat 84) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
