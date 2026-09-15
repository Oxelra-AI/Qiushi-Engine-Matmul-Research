import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0110 :
    QuotientRankAtLeast (spanCodes [258, 146, 86, 52, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(258, 496), (146, 256), (86, 270), (52, 336), (10, 173), (1, 511)]
    (codeMat 477) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane425GenSource0111 :
    QuotientRankAtLeast (spanCodes [258, 144, 86, 54, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(258, 162), (144, 2), (86, 270), (54, 256), (10, 173), (1, 511)]
    (codeMat 230) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane425GenSource0112 :
    QuotientRankAtLeast (spanCodes [258, 130, 86, 36, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 505), (130, 1), (86, 159), (36, 390), (10, 97), (1, 365)]
    (codeMat 405) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane425GenSource0113 :
    QuotientRankAtLeast (spanCodes [258, 134, 70, 36, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 301), (134, 329), (70, 402), (36, 360), (20, 328), (10, 80), (1, 128)]
    (codeMat 87) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane425GenSource0114 :
    QuotientRankAtLeast (spanCodes [258, 128, 70, 32, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 68), (128, 1), (70, 322), (32, 32), (22, 328), (10, 80), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane425GenSource0115 :
    QuotientRankAtLeast (spanCodes [258, 146, 86, 54, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 408), (146, 390), (86, 358), (54, 365), (10, 402), (1, 128)]
    (codeMat 102) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane425GenSource0116 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 34, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 391), (130, 1), (68, 322), (34, 440), (22, 456), (10, 208), (1, 128)]
    (codeMat 93) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane425GenSource0117 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 32, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 69), (128, 1), (68, 322), (32, 360), (22, 328), (10, 208), (1, 128)]
    (codeMat 92) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane425GenSource0118 :
    QuotientRankAtLeast (spanCodes [258, 134, 68, 38, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 263), (134, 451), (68, 322), (38, 312), (22, 280), (10, 208), (1, 128)]
    (codeMat 85) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane425GenSource0119 :
    QuotientRankAtLeast (spanCodes [258, 134, 70, 36, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 196), (134, 451), (70, 450), (36, 32), (22, 280), (10, 80), (1, 128)]
    (codeMat 92) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
