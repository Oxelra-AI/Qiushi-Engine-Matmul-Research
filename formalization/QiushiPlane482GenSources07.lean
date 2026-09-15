import QiushiPlane482GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit443From373
import QiushiMonoOrbit93From29
import QiushiOrbit35FP
import QiushiWcOrbit374Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane482GenSource0070 :
    QuotientRankAtLeast (spanCodes [440, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(440, 21), (84, 267), (1, 1)]
    (codeMat 241) (codeMat 423) (codeMat 181) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane482GenSource0071 :
    QuotientRankAtLeast (spanCodes [266, 176, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(266, 84), (176, 495), (84, 335), (1, 1)]
    (codeMat 225) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane482GenSource0072 :
    QuotientRankAtLeast (spanCodes [270, 178, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(270, 84), (178, 495), (84, 334), (1, 1)]
    (codeMat 233) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane482GenSource0073 :
    QuotientRankAtLeast (spanCodes [446, 84, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(446, 21), (84, 266), (1, 1)]
    (codeMat 249) (codeMat 423) (codeMat 181) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane482GenSource0074 :
    QuotientRankAtLeast (spanCodes [82, 48, 8, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 8, 2, 1] [(82, 70), (48, 18), (8, 9), (6, 16), (1, 8)]
    (codeMat 267) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit93_lb15_mono

theorem plane482GenSource0075 :
    QuotientRankAtLeast (spanCodes [140, 72, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 8, 2, 1] [(140, 84), (72, 24), (28, 68), (2, 2), (1, 3)]
    (codeMat 177) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit93_lb15_mono

theorem plane482GenSource0076 :
    QuotientRankAtLeast (spanCodes [258, 80, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 150), (80, 232), (34, 22), (10, 30), (4, 2), (1, 3)]
    (codeMat 401) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0077 :
    QuotientRankAtLeast (spanCodes [256, 66, 36, 22, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (66, 96), (36, 2), (22, 20), (8, 9), (1, 8)]
    (codeMat 267) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0078 :
    QuotientRankAtLeast (spanCodes [272, 148, 84, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 252), (148, 119), (84, 116), (12, 104), (2, 9), (1, 8)]
    (codeMat 169) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0079 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (128, 8), (64, 1), (20, 224), (10, 28), (1, 3)]
    (codeMat 172) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
