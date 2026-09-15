import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit192From65
import QiushiOrbit101FP
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0240 :
    QuotientRankAtLeast (spanCodes [128, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 9), (64, 8), (20, 166), (9, 32), (3, 2)]
    (codeMat 204) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0241 :
    QuotientRankAtLeast (spanCodes [128, 65, 21, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 3), (65, 8), (21, 132), (8, 32), (2, 2)]
    (codeMat 141) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0242 :
    QuotientRankAtLeast (spanCodes [133, 68, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(133, 132), (68, 166), (16, 1), (8, 9), (2, 2)]
    (codeMat 330) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0243 :
    QuotientRankAtLeast (spanCodes [148, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(148, 118), (84, 116), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane487GenSource0244 :
    QuotientRankAtLeast (spanCodes [146, 82, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(146, 128), (82, 383), (50, 10), (10, 42), (6, 1)]
    (codeMat 465) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane487GenSource0245 :
    QuotientRankAtLeast (spanCodes [128, 83, 32, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(128, 192), (83, 363), (32, 36), (10, 53), (7, 16)]
    (codeMat 267) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane487GenSource0246 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane487GenSource0247 :
    QuotientRankAtLeast (spanCodes [133, 68, 33, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(133, 96), (68, 232), (33, 30), (16, 1), (8, 3), (2, 8)]
    (codeMat 330) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0248 :
    QuotientRankAtLeast (spanCodes [129, 69, 37, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 136), (69, 224), (37, 28), (17, 10), (9, 3), (3, 8)]
    (codeMat 331) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0249 :
    QuotientRankAtLeast (spanCodes [132, 69, 32, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(132, 224), (69, 255), (32, 128), (17, 11), (9, 9), (3, 3)]
    (codeMat 275) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
