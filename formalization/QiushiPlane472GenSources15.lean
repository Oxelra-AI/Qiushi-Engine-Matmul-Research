import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0150 :
    QuotientRankAtLeast (spanCodes [258, 146, 81, 32, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 127), (146, 1), (81, 129), (32, 390), (10, 138), (5, 365)]
    (codeMat 351) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane472GenSource0151 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 33, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 100), (128, 63), (66, 502), (33, 160), (19, 440), (10, 112), (5, 128)]
    (codeMat 95) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane472GenSource0152 :
    QuotientRankAtLeast (spanCodes [259, 131, 65, 33, 16, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 196), (131, 197), (65, 390), (33, 160), (16, 360), (10, 240), (5, 128)]
    (codeMat 92) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane472GenSource0153 :
    QuotientRankAtLeast (spanCodes [260, 145, 84, 37, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(260, 390), (145, 149), (84, 409), (37, 274), (9, 128), (3, 365)]
    (codeMat 230) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane472GenSource0154 :
    QuotientRankAtLeast (spanCodes [256, 66, 34, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (66, 198), (34, 22), (18, 54), (10, 30), (4, 2), (1, 3)]
    (codeMat 273) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane472GenSource0155 :
    QuotientRankAtLeast (spanCodes [257, 64, 32, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 80), (64, 128), (32, 9), (16, 54), (9, 2), (4, 8), (3, 32)]
    (codeMat 267) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane472GenSource0156 :
    QuotientRankAtLeast (spanCodes [290, 130, 66, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(290, 28), (130, 219), (66, 89), (18, 216), (10, 88), (4, 32), (1, 8)]
    (codeMat 142) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane472GenSource0157 :
    QuotientRankAtLeast (spanCodes [272, 146, 80, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 126), (146, 511), (80, 252), (50, 392), (10, 224), (4, 384), (1, 256)]
    (codeMat 93) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0158 :
    QuotientRankAtLeast (spanCodes [273, 145, 80, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 157), (145, 31), (80, 284), (49, 149), (8, 511), (4, 1), (2, 3)]
    (codeMat 369) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0159 :
    QuotientRankAtLeast (spanCodes [257, 128, 81, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 257), (128, 130), (81, 149), (33, 264), (8, 360), (5, 256), (2, 128)]
    (codeMat 93) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
