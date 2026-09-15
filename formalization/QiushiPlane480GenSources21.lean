import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit43From14
import QiushiMonoOrbit89From23
import QiushiOrbit10FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0210 :
    QuotientRankAtLeast (spanCodes [448, 40, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(448, 4), (40, 9), (16, 8), (6, 128), (1, 130)]
    (codeMat 266) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane480GenSource0211 :
    QuotientRankAtLeast (spanCodes [258, 162, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 487), (162, 228), (66, 162), (16, 256), (10, 160), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0212 :
    QuotientRankAtLeast (spanCodes [256, 160, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (160, 68), (66, 162), (16, 256), (10, 160), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0213 :
    QuotientRankAtLeast (spanCodes [258, 130, 106, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 304), (130, 128), (106, 313), (16, 130), (4, 32), (1, 40)]
    (codeMat 335) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0214 :
    QuotientRankAtLeast (spanCodes [256, 128, 106, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 1), (128, 2), (106, 273), (16, 130), (4, 8), (1, 40)]
    (codeMat 396) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0215 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (160, 68), (64, 2), (16, 256), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0216 :
    QuotientRankAtLeast (spanCodes [288, 128, 76, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(288, 8), (128, 5), (76, 80), (16, 4), (2, 2), (1, 128)]
    (codeMat 142) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0217 :
    QuotientRankAtLeast (spanCodes [256, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (132, 160), (96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0218 :
    QuotientRankAtLeast (spanCodes [320, 168, 16, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(320, 8), (168, 80), (16, 128), (4, 4), (2, 2), (1, 5)]
    (codeMat 161) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0219 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 16, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(288, 432), (128, 8), (96, 416), (16, 64), (8, 256), (4, 6), (2, 1), (1, 4)]
    (codeMat 161) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
