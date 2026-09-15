import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit179Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0080 :
    QuotientRankAtLeast (spanCodes [132, 69, 37, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(132, 344), (69, 80), (37, 11), (20, 53), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane456GenSource0081 :
    QuotientRankAtLeast (spanCodes [160, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 224), (96, 96), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0082 :
    QuotientRankAtLeast (spanCodes [161, 96, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(161, 234), (96, 252), (17, 10), (9, 9), (5, 130), (3, 2)]
    (codeMat 267) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0083 :
    QuotientRankAtLeast (spanCodes [160, 100, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 232), (100, 126), (20, 30), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0084 :
    QuotientRankAtLeast (spanCodes [256, 161, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(256, 128), (161, 84), (20, 10), (8, 32), (2, 1)]
    (codeMat 273) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit179_lb15_wc

theorem plane456GenSource0085 :
    QuotientRankAtLeast (spanCodes [256, 161, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(256, 2), (161, 84), (16, 32), (10, 264), (4, 1)]
    (codeMat 161) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane456GenSource0086 :
    QuotientRankAtLeast (spanCodes [256, 161, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(256, 1), (161, 445), (17, 316), (10, 284), (5, 438)]
    (codeMat 412) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane456GenSource0087 :
    QuotientRankAtLeast (spanCodes [256, 161, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(256, 32), (161, 142), (18, 1), (10, 449), (6, 325)]
    (codeMat 163) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane456GenSource0088 :
    QuotientRankAtLeast (spanCodes [257, 129, 32, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 96), (129, 224), (32, 1), (16, 3), (10, 28), (4, 8)]
    (codeMat 266) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0089 :
    QuotientRankAtLeast (spanCodes [257, 130, 35, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(257, 91), (130, 365), (35, 62), (19, 30), (10, 53), (7, 63)]
    (codeMat 275) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

end QiushiMatmul
