import QiushiPlane482GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane482GenSource0090 :
    QuotientRankAtLeast (spanCodes [274, 138, 80, 42, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 118), (138, 105), (80, 227), (42, 150), (4, 128), (1, 130)]
    (codeMat 143) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0091 :
    QuotientRankAtLeast (spanCodes [270, 140, 74, 38, 30, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(270, 94), (140, 481), (74, 261), (38, 496), (30, 480), (1, 320)]
    (codeMat 87) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane482GenSource0092 :
    QuotientRankAtLeast (spanCodes [258, 148, 84, 32, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 480), (148, 255), (84, 239), (32, 260), (12, 69), (1, 320)]
    (codeMat 99) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane482GenSource0093 :
    QuotientRankAtLeast (spanCodes [292, 144, 84, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(292, 128), (144, 3), (84, 124), (12, 96), (2, 1), (1, 8)]
    (codeMat 185) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane482GenSource0094 :
    QuotientRankAtLeast (spanCodes [268, 130, 66, 36, 22, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(268, 490), (130, 260), (66, 261), (36, 16), (22, 160), (1, 320)]
    (codeMat 92) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane482GenSource0095 :
    QuotientRankAtLeast (spanCodes [276, 144, 84, 54, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(276, 507), (144, 27), (84, 491), (54, 260), (14, 261), (1, 320)]
    (codeMat 98) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane482GenSource0096 :
    QuotientRankAtLeast (spanCodes [258, 144, 84, 32, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 480), (144, 27), (84, 171), (32, 260), (12, 69), (1, 320)]
    (codeMat 107) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane482GenSource0097 :
    QuotientRankAtLeast (spanCodes [260, 132, 66, 34, 22, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 1), (132, 391), (66, 322), (34, 456), (22, 440), (12, 80), (1, 128)]
    (codeMat 85) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0098 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 36, 22, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 196), (134, 263), (66, 322), (36, 32), (22, 312), (14, 80), (1, 128)]
    (codeMat 93) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane482GenSource0099 :
    QuotientRankAtLeast (spanCodes [260, 132, 66, 34, 22, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 390), (132, 391), (66, 450), (34, 112), (22, 440), (14, 208), (1, 128)]
    (codeMat 92) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
