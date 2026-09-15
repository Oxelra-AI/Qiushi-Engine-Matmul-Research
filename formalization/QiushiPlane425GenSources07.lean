import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0070 :
    QuotientRankAtLeast (spanCodes [258, 176, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 119), (176, 252), (96, 28), (10, 104), (4, 9), (1, 8)]
    (codeMat 185) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0071 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 139), (130, 9), (64, 2), (20, 252), (10, 31), (1, 3)]
    (codeMat 165) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0072 :
    QuotientRankAtLeast (spanCodes [258, 178, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 126), (178, 252), (96, 20), (10, 104), (4, 9), (1, 8)]
    (codeMat 177) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0073 :
    QuotientRankAtLeast (spanCodes [258, 148, 68, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(258, 21), (148, 453), (68, 11), (50, 367), (10, 79), (1, 1)]
    (codeMat 489) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane425GenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 128, 82, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 316), (128, 32), (82, 296), (48, 63), (10, 265), (1, 365)]
    (codeMat 230) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane425GenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 144, 70, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 447), (144, 1), (70, 164), (52, 112), (10, 352), (1, 256)]
    (codeMat 94) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane425GenSource0076 :
    QuotientRankAtLeast (spanCodes [258, 146, 82, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 113), (146, 1), (82, 33), (36, 63), (10, 265), (1, 365)]
    (codeMat 167) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane425GenSource0077 :
    QuotientRankAtLeast (spanCodes [258, 148, 70, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 191), (148, 453), (70, 420), (54, 16), (10, 96), (1, 256)]
    (codeMat 94) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane425GenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 162, 66, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 28), (162, 252), (66, 20), (10, 148), (4, 3), (1, 2)]
    (codeMat 417) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane425GenSource0079 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 316), (128, 32), (80, 296), (54, 63), (10, 100), (1, 365)]
    (codeMat 167) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

end QiushiMatmul
