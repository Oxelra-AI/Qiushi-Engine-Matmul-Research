import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit111Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0100 :
    QuotientRankAtLeast (spanCodes [259, 134, 66, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 78), (134, 436), (66, 507), (34, 160), (20, 176), (10, 480)]
    (codeMat 157) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane454GenSource0101 :
    QuotientRankAtLeast (spanCodes [65, 33, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(65, 2), (33, 361), (20, 97), (9, 1), (3, 256)]
    (codeMat 107) (codeMat 423) (codeMat 181) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane454GenSource0102 :
    QuotientRankAtLeast (spanCodes [257, 130, 96, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(257, 439), (130, 3), (96, 441), (17, 316), (10, 284), (5, 438)]
    (codeMat 477) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane454GenSource0103 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 36, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 69), (130, 1), (68, 450), (36, 360), (20, 328), (10, 80), (1, 128)]
    (codeMat 85) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane454GenSource0104 :
    QuotientRankAtLeast (spanCodes [260, 133, 67, 35, 20, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(260, 511), (133, 430), (67, 268), (35, 252), (20, 175), (10, 269)]
    (codeMat 423) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane454GenSource0105 :
    QuotientRankAtLeast (spanCodes [260, 134, 65, 33, 20, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(260, 1), (134, 12), (65, 2), (33, 81), (20, 268), (10, 162)]
    (codeMat 461) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane454GenSource0106 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 35, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 1), (130, 390), (67, 323), (35, 328), (17, 240), (10, 408), (5, 128)]
    (codeMat 84) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane454GenSource0107 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 69), (130, 390), (64, 1), (32, 360), (19, 112), (10, 456), (7, 128)]
    (codeMat 92) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane454GenSource0108 :
    QuotientRankAtLeast (spanCodes [257, 131, 67, 35, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 274), (131, 429), (67, 374), (35, 80), (16, 360), (10, 240), (4, 128)]
    (codeMat 94) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane454GenSource0109 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(257, 68), (131, 391), (64, 1), (32, 32), (19, 440), (10, 456), (7, 128)]
    (codeMat 84) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
