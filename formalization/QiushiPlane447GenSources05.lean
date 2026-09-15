import QiushiPlane447GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit137From55
import QiushiOrbit23FP
import QiushiStep128Mono325From157
import QiushiWcOrbit113Dispatch
import QiushiWcOrbit114Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane447GenSource0050 :
    QuotientRankAtLeast (spanCodes [288, 160, 18, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [448, 36, 16, 1] [(288, 1), (160, 17), (18, 36), (1, 448)]
    (codeMat 230) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit325_lb15_mono

theorem plane447GenSource0051 :
    QuotientRankAtLeast (spanCodes [272, 130, 34, 8, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 80, 32, 2, 1] [(272, 304), (130, 320), (34, 80), (8, 2), (1, 3)]
    (codeMat 403) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit137_lb14_mono

theorem plane447GenSource0052 :
    QuotientRankAtLeast (spanCodes [274, 128, 64, 32, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 8, 2, 1] [(274, 96), (128, 8), (64, 1), (32, 384), (1, 2)]
    (codeMat 204) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit113_lb14_wc

theorem plane447GenSource0053 :
    QuotientRankAtLeast (spanCodes [278, 132, 72, 36, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(278, 160), (132, 418), (72, 8), (36, 256), (1, 9)]
    (codeMat 247) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane447GenSource0054 :
    QuotientRankAtLeast (spanCodes [256, 144, 48, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 8), (144, 216), (48, 128), (4, 1), (2, 3), (1, 4)]
    (codeMat 161) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

end QiushiMatmul
