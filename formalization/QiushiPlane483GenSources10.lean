import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit16Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0100 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 38, 20, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 457), (134, 502), (66, 402), (38, 456), (20, 112), (12, 80), (1, 128)]
    (codeMat 86) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane483GenSource0101 :
    QuotientRankAtLeast (spanCodes [264, 142, 70, 46, 30, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(264, 306), (142, 307), (70, 33), (46, 135), (30, 133), (1, 45)]
    (codeMat 277) (codeMat 443) (codeMat 254) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane483GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 12, 2, 1] [(258, 186), (128, 455), (68, 235), (32, 45), (20, 338), (10, 457), (1, 438)]
    (codeMat 239) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit16_lb12_wc

theorem plane483GenSource0103 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 38, 18, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (134, 480), (68, 104), (38, 284), (18, 511), (12, 97), (1, 8)]
    (codeMat 335) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane483GenSource0104 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 34, 18, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (130, 2), (66, 509), (34, 136), (18, 128), (14, 96), (1, 360)]
    (codeMat 213) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane483GenSource0105 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 22, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (128, 256), (66, 96), (32, 3), (22, 508), (14, 509), (1, 360)]
    (codeMat 298) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane483GenSource0106 :
    QuotientRankAtLeast (spanCodes [262, 134, 70, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 148), (134, 150), (70, 149), (38, 276), (22, 406), (10, 227), (1, 511)]
    (codeMat 412) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane483GenSource0107 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 34, 18, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (130, 3), (68, 68), (34, 424), (18, 24), (14, 160), (1, 256)]
    (codeMat 93) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane483GenSource0108 :
    QuotientRankAtLeast (spanCodes [262, 134, 70, 38, 18, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 480), (134, 224), (70, 96), (38, 31), (18, 3), (8, 9), (1, 8)]
    (codeMat 267) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane483GenSource0109 :
    QuotientRankAtLeast (spanCodes [260, 128, 66, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 2), (128, 325), (66, 68), (32, 16), (20, 168), (12, 160), (1, 256)]
    (codeMat 85) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
