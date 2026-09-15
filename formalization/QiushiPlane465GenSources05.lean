import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0050 :
    QuotientRankAtLeast (spanCodes [262, 131, 68, 32, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 378), (131, 191), (68, 367), (32, 432), (22, 180), (10, 420)]
    (codeMat 206) (codeMat 379) (codeMat 247) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane465GenSource0051 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 38, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (129, 490), (68, 287), (38, 176), (18, 16), (10, 336)]
    (codeMat 159) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane465GenSource0052 :
    QuotientRankAtLeast (spanCodes [304, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 232), (178, 245), (66, 21), (10, 149), (6, 3), (1, 2)]
    (codeMat 417) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0053 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 39, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 10), (132, 11), (68, 203), (39, 160), (21, 180), (10, 420)]
    (codeMat 205) (codeMat 123) (codeMat 236) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane465GenSource0054 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 38, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 139), (128, 9), (68, 252), (38, 136), (16, 8), (10, 104)]
    (codeMat 214) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0055 :
    QuotientRankAtLeast (spanCodes [259, 132, 68, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 357), (132, 463), (68, 203), (39, 356), (20, 127), (10, 420)]
    (codeMat 239) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane465GenSource0056 :
    QuotientRankAtLeast (spanCodes [257, 134, 68, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 78), (134, 437), (68, 79), (35, 160), (18, 320), (10, 336)]
    (codeMat 213) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane465GenSource0057 :
    QuotientRankAtLeast (spanCodes [304, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 224), (178, 104), (64, 3), (10, 148), (4, 128), (1, 2)]
    (codeMat 141) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0058 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 391), (130, 1), (68, 322), (38, 440), (20, 456), (10, 80), (1, 128)]
    (codeMat 85) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane465GenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 36, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 228), (130, 219), (68, 274), (36, 32), (22, 280), (10, 80), (1, 128)]
    (codeMat 95) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
