import QiushiPlane474GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane474GenSource0100 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 68), (131, 391), (64, 1), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 84) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane474GenSource0101 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 33, 18, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 390), (131, 69), (65, 1), (33, 112), (18, 360), (10, 328), (7, 128)]
    (codeMat 85) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane474GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 35, 16, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 68), (131, 197), (67, 323), (35, 160), (16, 360), (10, 408), (7, 128)]
    (codeMat 93) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane474GenSource0103 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 32, 19, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 228), (129, 457), (66, 502), (32, 32), (19, 456), (10, 112), (5, 128)]
    (codeMat 87) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane474GenSource0104 :
    QuotientRankAtLeast (spanCodes [257, 64, 32, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 208), (64, 128), (32, 3), (17, 20), (8, 2), (5, 8), (2, 32)]
    (codeMat 266) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane474GenSource0105 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 22), (129, 81), (64, 130), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 142) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane474GenSource0106 :
    QuotientRankAtLeast (spanCodes [258, 128, 82, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 393), (128, 511), (82, 284), (34, 392), (10, 224), (6, 384), (1, 256)]
    (codeMat 94) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0107 :
    QuotientRankAtLeast (spanCodes [273, 145, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 501), (145, 503), (81, 502), (49, 176), (9, 432), (5, 24), (3, 8)]
    (codeMat 140) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane474GenSource0108 :
    QuotientRankAtLeast (spanCodes [257, 128, 80, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 21), (128, 8), (80, 96), (33, 149), (8, 360), (4, 2), (2, 1)]
    (codeMat 417) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane474GenSource0109 :
    QuotientRankAtLeast (spanCodes [272, 145, 80, 48, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 136), (145, 28), (80, 480), (48, 128), (8, 256), (4, 1), (2, 3)]
    (codeMat 177) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
