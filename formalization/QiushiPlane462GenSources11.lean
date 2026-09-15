import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit68Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0110 :
    QuotientRankAtLeast (spanCodes [306, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(306, 246), (178, 255), (64, 1), (10, 150), (4, 128), (1, 2)]
    (codeMat 140) (codeMat 403) (codeMat 403) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane462GenSource0111 :
    QuotientRankAtLeast (spanCodes [258, 160, 67, 18, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 164, 68, 16, 10, 1] [(258, 357), (160, 68), (67, 251), (18, 288), (10, 224), (7, 16)]
    (codeMat 142) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit68_lb14_unconditional

theorem plane462GenSource0112 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 263), (132, 451), (68, 450), (34, 312), (20, 280), (10, 80), (1, 128)]
    (codeMat 92) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0113 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 32, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 100), (132, 329), (68, 402), (32, 32), (22, 328), (10, 80), (1, 128)]
    (codeMat 87) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0114 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 33, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 451), (133, 450), (68, 196), (33, 280), (20, 208), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0115 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 36, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 68), (129, 450), (68, 69), (36, 32), (21, 208), (8, 360), (2, 128)]
    (codeMat 93) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0116 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 32, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 301), (133, 502), (68, 100), (32, 360), (20, 240), (9, 32), (3, 128)]
    (codeMat 94) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0117 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 33, 21, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 329), (133, 374), (68, 100), (33, 328), (21, 240), (9, 32), (3, 128)]
    (codeMat 95) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0118 :
    QuotientRankAtLeast (spanCodes [256, 129, 68, 37, 21, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 219), (129, 191), (68, 429), (37, 408), (21, 440), (9, 360), (3, 128)]
    (codeMat 87) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0119 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 37, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 374), (128, 63), (68, 429), (37, 240), (20, 440), (9, 360), (3, 128)]
    (codeMat 86) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
