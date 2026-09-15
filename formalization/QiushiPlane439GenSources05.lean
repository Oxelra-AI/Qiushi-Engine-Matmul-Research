import QiushiPlane439GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit121From55
import QiushiMonoOrbit192From65
import QiushiOrbit11FP
import QiushiStep99Orbit34Dispatch
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit114Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane439GenSource0050 :
    QuotientRankAtLeast (spanCodes [136, 40, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(136, 133), (40, 1), (16, 2), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane439GenSource0051 :
    QuotientRankAtLeast (spanCodes [160, 64, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(160, 272), (64, 2), (20, 96), (2, 8), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane439GenSource0052 :
    QuotientRankAtLeast (spanCodes [128, 76, 32, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(128, 128), (76, 268), (32, 1), (20, 10), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane439GenSource0053 :
    QuotientRankAtLeast (spanCodes [260, 160, 20, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(260, 128), (160, 341), (20, 42), (12, 10), (1, 1)]
    (codeMat 337) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane439GenSource0054 :
    QuotientRankAtLeast (spanCodes [160, 72, 18, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(160, 162), (72, 8), (18, 256), (6, 2), (1, 1)]
    (codeMat 241) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane439GenSource0055 :
    QuotientRankAtLeast (spanCodes [130, 70, 34, 20, 8, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 20, 8, 2, 1] [(130, 256), (70, 88), (34, 22), (20, 20), (8, 9), (1, 8)]
    (codeMat 331) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit34_lb14_unconditional

theorem plane439GenSource0056 :
    QuotientRankAtLeast (spanCodes [256, 160, 16, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(256, 8), (160, 96), (16, 256), (4, 1), (1, 2)]
    (codeMat 161) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane439GenSource0057 :
    QuotientRankAtLeast (spanCodes [258, 130, 34, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(258, 34), (130, 32), (34, 15), (20, 14), (1, 384)]
    (codeMat 355) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane439GenSource0058 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (128, 54), (68, 82), (32, 8), (20, 112), (12, 80), (1, 128)]
    (codeMat 86) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
