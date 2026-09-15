import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1120 :
    QuotientRankAtLeast (spanCodes [321, 192, 33, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(321, 71), (192, 128), (33, 55), (16, 40), (9, 63), (5, 1), (3, 2)]
    (codeMat 273) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1121 :
    QuotientRankAtLeast (spanCodes [321, 193, 33, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(321, 71), (193, 199), (33, 55), (16, 32), (9, 63), (5, 1), (3, 3)]
    (codeMat 273) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1122 :
    QuotientRankAtLeast (spanCodes [257, 129, 32, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 112), (129, 240), (32, 1), (16, 3), (9, 54), (4, 8), (3, 40)]
    (codeMat 266) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1123 :
    QuotientRankAtLeast (spanCodes [321, 193, 32, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(321, 120), (193, 248), (32, 54), (17, 28), (8, 63), (5, 8), (2, 32)]
    (codeMat 267) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1124 :
    QuotientRankAtLeast (spanCodes [384, 33, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(384, 4), (33, 80), (17, 81), (8, 8), (4, 128), (2, 130)]
    (codeMat 266) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1125 :
    QuotientRankAtLeast (spanCodes [257, 128, 32, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 68), (128, 128), (32, 8), (17, 20), (8, 32), (4, 1), (2, 2)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1126 :
    QuotientRankAtLeast (spanCodes [256, 130, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (130, 216), (34, 10), (18, 3), (10, 60), (6, 8), (1, 32)]
    (codeMat 267) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1127 :
    QuotientRankAtLeast (spanCodes [258, 128, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (128, 128), (34, 11), (18, 2), (10, 52), (6, 8), (1, 32)]
    (codeMat 267) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1128 :
    QuotientRankAtLeast (spanCodes [320, 194, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(320, 128), (194, 248), (34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1129 :
    QuotientRankAtLeast (spanCodes [322, 192, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(322, 248), (192, 128), (34, 62), (18, 63), (10, 61), (6, 8), (1, 40)]
    (codeMat 266) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
