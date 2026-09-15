import QiushiPlane455GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane455GenSource0090 :
    QuotientRankAtLeast (spanCodes [261, 129, 69, 37, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 374), (129, 191), (69, 429), (37, 240), (20, 440), (9, 360), (3, 128)]
    (codeMat 87) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane455GenSource0091 :
    QuotientRankAtLeast (spanCodes [322, 129, 33, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(322, 15), (129, 440), (33, 164), (16, 32), (10, 304), (4, 438)]
    (codeMat 157) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane455GenSource0092 :
    QuotientRankAtLeast (spanCodes [290, 128, 96, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 131), (128, 9), (96, 252), (18, 8), (10, 352), (6, 128), (1, 256)]
    (codeMat 95) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0093 :
    QuotientRankAtLeast (spanCodes [289, 129, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 259), (129, 23), (96, 284), (17, 149), (8, 511), (5, 3), (2, 2)]
    (codeMat 481) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0094 :
    QuotientRankAtLeast (spanCodes [289, 129, 96, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 246), (129, 257), (96, 373), (16, 8), (9, 360), (4, 384), (3, 256)]
    (codeMat 85) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane455GenSource0095 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (129, 327), (65, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 92) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane455GenSource0096 :
    QuotientRankAtLeast (spanCodes [288, 128, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(288, 54), (128, 219), (66, 81), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 143) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane455GenSource0097 :
    QuotientRankAtLeast (spanCodes [322, 128, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(322, 208), (128, 128), (32, 54), (18, 2), (10, 61), (6, 32), (1, 40)]
    (codeMat 267) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane455GenSource0098 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (129, 70), (66, 71), (32, 16), (18, 432), (10, 440), (6, 256)]
    (codeMat 85) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane455GenSource0099 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 10), (129, 30), (66, 29), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 461) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
