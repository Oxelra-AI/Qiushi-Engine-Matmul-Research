import QiushiPlane324GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit43From14
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep99Orbit55Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane324GenSource0020 :
    QuotientRankAtLeast (spanCodes [268, 132, 64, 36, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(268, 15), (132, 137), (64, 2), (36, 45), (16, 438), (1, 3)]
    (codeMat 421) (codeMat 183) (codeMat 419) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane324GenSource0021 :
    QuotientRankAtLeast (spanCodes [130, 66, 32, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(130, 128), (66, 304), (32, 1), (16, 2), (4, 8), (1, 32)]
    (codeMat 330) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane324GenSource0022 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 128), (128, 8), (68, 160), (36, 130), (16, 9), (1, 432)]
    (codeMat 358) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane324GenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (132, 196), (64, 2), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 84) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane324GenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 130, 70, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (130, 9), (70, 413), (36, 128), (16, 8), (10, 96), (1, 360)]
    (codeMat 215) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane324GenSource0025 :
    QuotientRankAtLeast (spanCodes [328, 192, 32, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(328, 136), (192, 432), (32, 8), (16, 40), (4, 1), (1, 3)]
    (codeMat 401) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane324GenSource0026 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 381), (128, 130), (68, 105), (36, 360), (16, 128), (12, 104), (1, 8)]
    (codeMat 142) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane324GenSource0027 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(258, 13), (130, 4), (64, 18), (34, 352), (16, 256), (6, 8), (1, 16)]
    (codeMat 141) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane324GenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane324GenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (66, 70), (34, 88), (16, 8), (10, 112), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
