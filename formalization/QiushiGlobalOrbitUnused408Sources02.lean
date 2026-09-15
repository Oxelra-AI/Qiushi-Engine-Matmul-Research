import QiushiGlobalOrbitUnused408Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane408UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 77), (128, 432), (65, 1), (32, 256), (21, 237), (9, 9), (3, 511)]
    (codeMat 181) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane408UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 68), (128, 1), (66, 70), (35, 238), (18, 9), (10, 441), (4, 325)]
    (codeMat 380) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane408UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 131, 66, 32, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (131, 483), (66, 287), (32, 2), (16, 130), (10, 278), (6, 256)]
    (codeMat 86) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane408UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 33, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (130, 9), (67, 126), (33, 148), (17, 404), (10, 278), (6, 384)]
    (codeMat 157) (codeMat 382) (codeMat 499) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane408UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 33, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 28), (130, 2), (67, 22), (33, 483), (16, 130), (10, 278), (7, 9)]
    (codeMat 485) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
