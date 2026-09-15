import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit144Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0290 :
    QuotientRankAtLeast (spanCodes [386, 34, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(386, 120), (34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0291 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (132, 34), (64, 1), (19, 441), (10, 119)]
    (codeMat 428) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0292 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(261, 33), (133, 34), (64, 1), (19, 441), (10, 119)]
    (codeMat 428) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0293 :
    QuotientRankAtLeast (spanCodes [288, 160, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 32), (160, 35), (64, 1), (19, 441), (10, 462)]
    (codeMat 372) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0294 :
    QuotientRankAtLeast (spanCodes [290, 162, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(290, 495), (162, 493), (64, 1), (19, 441), (10, 462)]
    (codeMat 372) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0295 :
    QuotientRankAtLeast (spanCodes [292, 164, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 32), (164, 34), (64, 1), (19, 119), (10, 462)]
    (codeMat 380) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0296 :
    QuotientRankAtLeast (spanCodes [295, 167, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(295, 495), (167, 492), (64, 1), (19, 119), (10, 462)]
    (codeMat 380) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0297 :
    QuotientRankAtLeast (spanCodes [260, 133, 65, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 2), (133, 35), (65, 1), (19, 462), (10, 119)]
    (codeMat 421) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0298 :
    QuotientRankAtLeast (spanCodes [288, 162, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 3), (162, 411), (66, 440), (19, 462), (10, 441)]
    (codeMat 358) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0299 :
    QuotientRankAtLeast (spanCodes [292, 167, 67, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 2), (167, 410), (67, 440), (19, 119), (10, 441)]
    (codeMat 359) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
