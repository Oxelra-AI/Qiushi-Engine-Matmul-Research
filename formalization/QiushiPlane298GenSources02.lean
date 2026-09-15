import QiushiPlane298GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep99Mono3032
import QiushiWcOrbit113Dispatch
import QiushiWcOrbit114Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane298GenSource0020 :
    QuotientRankAtLeast (spanCodes [384, 64, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 8, 2, 1] [(384, 2), (64, 1), (32, 384), (10, 96), (1, 8)]
    (codeMat 140) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit113_lb14_wc

theorem plane298GenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 128, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(256, 1), (128, 2), (32, 8), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane298GenSource0022 :
    QuotientRankAtLeast (spanCodes [384, 32, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 8, 2, 1] [(384, 128), (32, 9), (18, 3), (10, 60), (4, 8), (1, 32)]
    (codeMat 267) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_32_lb12

theorem plane298GenSource0023 :
    QuotientRankAtLeast (spanCodes [384, 66, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(384, 128), (66, 198), (32, 32), (18, 54), (10, 30), (6, 2), (1, 3)]
    (codeMat 273) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane298GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 22), (130, 54), (66, 30), (32, 128), (10, 198), (4, 2), (1, 3)]
    (codeMat 161) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane298GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 22), (130, 54), (64, 8), (32, 128), (10, 70), (4, 2), (1, 1)]
    (codeMat 161) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane298GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 132, 80, 32, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (132, 352), (80, 148), (32, 1), (8, 2), (2, 256), (1, 128)]
    (codeMat 106) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane298GenSource0027 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (132, 326), (68, 324), (32, 40), (20, 368), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
