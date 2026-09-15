import QiushiPlane292GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit102From32
import QiushiMonoOrbit106From34
import QiushiOrbit11FP
import QiushiWcOrbit114Dispatch
import QiushiWcOrbit119Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane292GenSource0020 :
    QuotientRankAtLeast (spanCodes [128, 32, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 8, 2, 1] [(128, 8), (32, 2), (16, 1), (10, 68), (1, 256)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit106_lb14_mono

theorem plane292GenSource0021 :
    QuotientRankAtLeast (spanCodes [128, 32, 18, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(128, 256), (32, 2), (18, 32), (10, 33), (1, 45)]
    (codeMat 282) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane292GenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 128, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(256, 1), (128, 2), (32, 8), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane292GenSource0023 :
    QuotientRankAtLeast (spanCodes [128, 32, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 8, 2, 1] [(128, 128), (32, 32), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit102_lb12_mono

theorem plane292GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 20), (128, 32), (66, 28), (32, 128), (10, 196), (4, 2), (1, 3)]
    (codeMat 161) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane292GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 34), (128, 54), (64, 9), (32, 128), (10, 112), (6, 32), (1, 8)]
    (codeMat 141) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane292GenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 20), (128, 32), (64, 8), (32, 128), (10, 68), (4, 2), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane292GenSource0027 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 69), (128, 1), (66, 70), (32, 40), (16, 8), (10, 112), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
