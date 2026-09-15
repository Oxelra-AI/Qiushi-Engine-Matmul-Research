import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit231Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0300 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (128, 1), (68, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0301 :
    QuotientRankAtLeast (spanCodes [256, 133, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (133, 35), (69, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0302 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(262, 33), (128, 1), (70, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0303 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 3), (130, 1), (70, 34), (19, 119), (10, 441)]
    (codeMat 421) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0304 :
    QuotientRankAtLeast (spanCodes [259, 133, 70, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(259, 33), (133, 34), (70, 35), (19, 441), (10, 462)]
    (codeMat 421) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0305 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 3), (134, 35), (70, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0306 :
    QuotientRankAtLeast (spanCodes [292, 162, 70, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(292, 511), (162, 495), (70, 272), (19, 413), (10, 238)]
    (codeMat 302) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane484GenSource0307 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 32), (128, 1), (96, 34), (19, 462), (10, 119)]
    (codeMat 372) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0308 :
    QuotientRankAtLeast (spanCodes [291, 128, 99, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(291, 495), (128, 1), (99, 492), (19, 462), (10, 119)]
    (codeMat 372) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0309 :
    QuotientRankAtLeast (spanCodes [288, 131, 99, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 2), (131, 440), (99, 410), (19, 441), (10, 119)]
    (codeMat 358) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
