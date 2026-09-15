import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0160 :
    QuotientRankAtLeast (spanCodes [259, 131, 65, 33, 16, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 196), (131, 197), (65, 390), (33, 160), (16, 360), (10, 240), (5, 128)]
    (codeMat 92) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane470GenSource0161 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 17, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 402), (128, 219), (65, 63), (34, 80), (17, 280), (10, 312), (4, 128)]
    (codeMat 94) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane470GenSource0162 :
    QuotientRankAtLeast (spanCodes [256, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(256, 256), (80, 80), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane470GenSource0163 :
    QuotientRankAtLeast (spanCodes [256, 64, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(256, 256), (64, 4), (20, 80), (8, 2), (2, 8), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane470GenSource0164 :
    QuotientRankAtLeast (spanCodes [258, 66, 32, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 70), (66, 198), (32, 8), (18, 54), (10, 30), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane470GenSource0165 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 30), (128, 3), (64, 1), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 140) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane470GenSource0166 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (129, 10), (65, 3), (16, 128), (9, 216), (5, 40), (3, 8)]
    (codeMat 141) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane470GenSource0167 :
    QuotientRankAtLeast (spanCodes [257, 129, 81, 32, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 136), (129, 480), (81, 28), (32, 1), (8, 3), (5, 128), (2, 256)]
    (codeMat 106) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0168 :
    QuotientRankAtLeast (spanCodes [257, 145, 81, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 510), (145, 30), (81, 374), (48, 256), (8, 384), (5, 1), (2, 3)]
    (codeMat 177) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane470GenSource0169 :
    QuotientRankAtLeast (spanCodes [257, 144, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 259), (144, 8), (81, 393), (49, 362), (8, 511), (5, 3), (2, 1)]
    (codeMat 369) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
