import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit74From17
import QiushiOrbit35FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit67Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0100 :
    QuotientRankAtLeast (spanCodes [322, 138, 40, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(322, 22), (138, 119), (40, 1), (16, 9), (4, 128), (1, 130)]
    (codeMat 266) (codeMat 339) (codeMat 467) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0101 :
    QuotientRankAtLeast (spanCodes [262, 132, 74, 46, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 164, 68, 16, 10, 1] [(262, 284), (132, 251), (74, 10), (46, 440), (20, 224), (1, 16)]
    (codeMat 143) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit67_lb15_unconditional

theorem plane481GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 134, 76, 32, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 332), (134, 101), (76, 21), (32, 365), (20, 100), (1, 63)]
    (codeMat 247) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane481GenSource0103 :
    QuotientRankAtLeast (spanCodes [260, 134, 76, 38, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(260, 365), (134, 100), (76, 21), (38, 332), (20, 101), (1, 63)]
    (codeMat 311) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane481GenSource0104 :
    QuotientRankAtLeast (spanCodes [330, 136, 42, 18, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(330, 247), (136, 227), (42, 11), (18, 8), (6, 128), (1, 130)]
    (codeMat 267) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0105 :
    QuotientRankAtLeast (spanCodes [392, 66, 34, 18, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(392, 28), (66, 97), (34, 129), (18, 130), (6, 1), (1, 8)]
    (codeMat 281) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0106 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 374), (130, 219), (68, 402), (34, 240), (20, 408), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane481GenSource0107 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 502), (134, 457), (68, 402), (38, 112), (20, 456), (10, 208), (1, 128)]
    (codeMat 95) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane481GenSource0108 :
    QuotientRankAtLeast (spanCodes [262, 130, 76, 36, 20, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 192, 32, 20, 10, 1] [(262, 430), (130, 325), (76, 20), (36, 432), (20, 368), (1, 32)]
    (codeMat 143) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit74_lb14_mono

theorem plane481GenSource0109 :
    QuotientRankAtLeast (spanCodes [256, 130, 70, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 63), (130, 219), (70, 274), (34, 312), (20, 280), (10, 80), (1, 128)]
    (codeMat 95) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
