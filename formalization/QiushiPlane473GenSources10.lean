import QiushiPlane473GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane473GenSource0100 :
    QuotientRankAtLeast (spanCodes [259, 129, 65, 35, 16, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 457), (129, 228), (65, 219), (35, 456), (16, 32), (10, 280), (5, 128)]
    (codeMat 86) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane473GenSource0101 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 17, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 402), (128, 219), (65, 63), (34, 80), (17, 280), (10, 312), (4, 128)]
    (codeMat 94) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane473GenSource0102 :
    QuotientRankAtLeast (spanCodes [272, 144, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 381), (144, 511), (82, 252), (50, 23), (10, 31), (6, 2), (1, 3)]
    (codeMat 337) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0103 :
    QuotientRankAtLeast (spanCodes [272, 145, 81, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 510), (145, 374), (81, 30), (48, 1), (8, 3), (5, 256), (2, 384)]
    (codeMat 106) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0104 :
    QuotientRankAtLeast (spanCodes [273, 145, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 501), (145, 503), (81, 502), (49, 176), (9, 432), (5, 24), (3, 8)]
    (codeMat 140) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0105 :
    QuotientRankAtLeast (spanCodes [272, 145, 80, 49, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 119), (145, 255), (80, 287), (49, 129), (9, 3), (4, 384), (3, 256)]
    (codeMat 107) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0106 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 254), (144, 511), (80, 381), (48, 8), (9, 360), (4, 384), (3, 128)]
    (codeMat 85) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0107 :
    QuotientRankAtLeast (spanCodes [272, 146, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 406), (146, 256), (82, 255), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 465) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0108 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 70), (68, 68), (36, 8), (16, 432), (10, 160), (1, 256)]
    (codeMat 92) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0109 :
    QuotientRankAtLeast (spanCodes [256, 132, 69, 37, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (132, 68), (69, 326), (37, 424), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
