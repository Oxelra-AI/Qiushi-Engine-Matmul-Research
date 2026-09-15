import QiushiPlane469GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane469GenSource0130 :
    QuotientRankAtLeast (spanCodes [258, 129, 64, 35, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 457), (129, 374), (64, 219), (35, 328), (17, 240), (10, 408), (5, 128)]
    (codeMat 87) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane469GenSource0131 :
    QuotientRankAtLeast (spanCodes [258, 135, 66, 38, 22, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 138), (135, 235), (66, 487), (38, 10), (22, 11), (10, 31)]
    (codeMat 458) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane469GenSource0132 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 35, 16, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 68), (131, 197), (67, 323), (35, 160), (16, 360), (10, 408), (7, 128)]
    (codeMat 93) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane469GenSource0133 :
    QuotientRankAtLeast (spanCodes [258, 161, 66, 16, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 149), (161, 116), (66, 148), (16, 128), (10, 274), (6, 365)]
    (codeMat 188) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane469GenSource0134 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 33, 17, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 402), (131, 374), (65, 219), (33, 208), (17, 240), (10, 408), (4, 128)]
    (codeMat 86) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane469GenSource0135 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 20), (128, 2), (64, 1), (16, 128), (10, 80), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane469GenSource0136 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 374), (144, 3), (80, 508), (48, 360), (10, 480), (4, 384), (1, 256)]
    (codeMat 94) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0137 :
    QuotientRankAtLeast (spanCodes [258, 128, 82, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 393), (128, 511), (82, 284), (34, 392), (10, 224), (6, 384), (1, 256)]
    (codeMat 94) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0138 :
    QuotientRankAtLeast (spanCodes [256, 145, 80, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (145, 374), (80, 245), (49, 96), (8, 360), (4, 128), (2, 384)]
    (codeMat 93) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0139 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (144, 3), (81, 484), (49, 416), (8, 256), (5, 8), (2, 24)]
    (codeMat 142) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
