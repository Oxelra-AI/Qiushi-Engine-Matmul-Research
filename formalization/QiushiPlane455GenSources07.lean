import QiushiPlane455GenData
import QiushiCertifiedTransport
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane455GenSource0070 :
    QuotientRankAtLeast (spanCodes [321, 129, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(321, 495), (129, 493), (38, 441), (20, 462), (10, 118)]
    (codeMat 482) (codeMat 351) (codeMat 239) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane455GenSource0071 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 437), (129, 79), (64, 1), (36, 320), (20, 336), (10, 496)]
    (codeMat 212) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane455GenSource0072 :
    QuotientRankAtLeast (spanCodes [262, 129, 65, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 496), (129, 336), (65, 16), (32, 1), (20, 79), (10, 506)]
    (codeMat 298) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane455GenSource0073 :
    QuotientRankAtLeast (spanCodes [256, 129, 69, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(256, 45), (129, 34), (69, 46), (20, 170), (9, 438), (3, 32)]
    (codeMat 461) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane455GenSource0074 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 32, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 228), (128, 219), (68, 402), (32, 32), (20, 280), (10, 208), (1, 128)]
    (codeMat 87) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane455GenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 129, 67, 32, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 197), (129, 451), (67, 263), (32, 360), (17, 280), (10, 312), (5, 128)]
    (codeMat 92) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane455GenSource0076 :
    QuotientRankAtLeast (spanCodes [258, 129, 64, 35, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 457), (129, 374), (64, 219), (35, 328), (17, 240), (10, 408), (5, 128)]
    (codeMat 87) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane455GenSource0077 :
    QuotientRankAtLeast (spanCodes [257, 129, 67, 35, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 129), (129, 263), (67, 451), (35, 328), (17, 312), (10, 280), (5, 128)]
    (codeMat 93) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane455GenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 129, 67, 35, 18, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 191), (129, 301), (67, 329), (35, 312), (18, 360), (10, 328), (6, 128)]
    (codeMat 87) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane455GenSource0079 :
    QuotientRankAtLeast (spanCodes [321, 129, 34, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(321, 136), (129, 139), (34, 274), (19, 166), (10, 306), (7, 2)]
    (codeMat 141) (codeMat 346) (codeMat 459) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
