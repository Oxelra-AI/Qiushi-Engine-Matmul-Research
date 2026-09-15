import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0200 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 68), (131, 391), (64, 1), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 84) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane471GenSource0201 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 33, 18, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 390), (131, 69), (65, 1), (33, 112), (18, 360), (10, 328), (7, 128)]
    (codeMat 85) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane471GenSource0202 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 35, 16, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 68), (131, 197), (67, 323), (35, 160), (16, 360), (10, 408), (7, 128)]
    (codeMat 93) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane471GenSource0203 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 19, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 196), (128, 390), (65, 1), (34, 160), (19, 112), (10, 456), (6, 128)]
    (codeMat 93) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane471GenSource0204 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 17, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 402), (128, 219), (65, 63), (34, 80), (17, 280), (10, 312), (4, 128)]
    (codeMat 94) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane471GenSource0205 :
    QuotientRankAtLeast (spanCodes [273, 132, 84, 48, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(273, 370), (132, 255), (84, 498), (48, 504), (9, 1), (3, 365)]
    (codeMat 379) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane471GenSource0206 :
    QuotientRankAtLeast (spanCodes [289, 128, 65, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 30), (128, 130), (65, 219), (16, 128), (9, 216), (5, 40), (3, 8)]
    (codeMat 142) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane471GenSource0207 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 22), (129, 81), (64, 130), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 142) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane471GenSource0208 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 48, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 156), (144, 8), (80, 352), (48, 128), (8, 256), (4, 3), (2, 1)]
    (codeMat 177) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0209 :
    QuotientRankAtLeast (spanCodes [272, 144, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 139), (144, 130), (81, 509), (49, 264), (8, 360), (5, 384), (2, 128)]
    (codeMat 95) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
