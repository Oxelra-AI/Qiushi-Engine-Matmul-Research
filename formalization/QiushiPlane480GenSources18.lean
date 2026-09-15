import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiMonoOrbit89From23
import QiushiOrbit10FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0180 :
    QuotientRankAtLeast (spanCodes [288, 128, 72, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(288, 4), (128, 9), (72, 2), (16, 8), (1, 128)]
    (codeMat 86) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane480GenSource0181 :
    QuotientRankAtLeast (spanCodes [260, 140, 72, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 432), (140, 443), (72, 2), (40, 32), (16, 40), (1, 130)]
    (codeMat 470) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0182 :
    QuotientRankAtLeast (spanCodes [268, 140, 64, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(268, 400), (140, 403), (64, 2), (40, 32), (16, 40), (1, 130)]
    (codeMat 340) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0183 :
    QuotientRankAtLeast (spanCodes [268, 140, 72, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(268, 304), (140, 313), (72, 2), (32, 32), (16, 40), (1, 130)]
    (codeMat 470) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0184 :
    QuotientRankAtLeast (spanCodes [260, 140, 64, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 1), (140, 273), (64, 128), (32, 8), (16, 40), (1, 130)]
    (codeMat 277) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0185 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 8), (160, 80), (64, 1), (16, 128), (8, 2), (1, 4)]
    (codeMat 84) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0186 :
    QuotientRankAtLeast (spanCodes [390, 70, 32, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(390, 216), (70, 208), (32, 4), (16, 7), (8, 2), (1, 128)]
    (codeMat 98) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0187 :
    QuotientRankAtLeast (spanCodes [260, 130, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (130, 2), (68, 324), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0188 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (128, 2), (68, 324), (34, 168), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0189 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 327), (128, 2), (70, 324), (34, 184), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
