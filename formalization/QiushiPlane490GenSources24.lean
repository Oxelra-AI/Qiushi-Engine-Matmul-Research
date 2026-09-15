import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiOrbit35FP
import QiushiWcOrbit157Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0240 :
    QuotientRankAtLeast (spanCodes [272, 192, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(272, 164), (192, 2), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0241 :
    QuotientRankAtLeast (spanCodes [272, 132, 68, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 224), (132, 28), (68, 20), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0242 :
    QuotientRankAtLeast (spanCodes [274, 128, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 118), (128, 9), (64, 1), (10, 22), (4, 128), (1, 2)]
    (codeMat 140) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0243 :
    QuotientRankAtLeast (spanCodes [274, 130, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 232), (130, 8), (64, 3), (10, 20), (6, 128), (1, 2)]
    (codeMat 141) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0244 :
    QuotientRankAtLeast (spanCodes [274, 128, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 126), (128, 9), (64, 1), (10, 22), (6, 130), (1, 2)]
    (codeMat 140) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0245 :
    QuotientRankAtLeast (spanCodes [274, 130, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 246), (130, 9), (64, 3), (10, 22), (4, 128), (1, 2)]
    (codeMat 141) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0246 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(256, 128), (131, 52), (65, 32), (19, 53), (10, 30)]
    (codeMat 358) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane490GenSource0247 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 175), (128, 2), (67, 42), (18, 3), (10, 35)]
    (codeMat 167) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0248 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 175), (130, 40), (66, 42), (18, 32), (10, 35)]
    (codeMat 230) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0249 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(257, 118), (128, 1), (64, 9), (18, 2), (10, 34)]
    (codeMat 156) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

end QiushiMatmul
