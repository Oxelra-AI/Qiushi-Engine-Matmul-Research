import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0200 :
    QuotientRankAtLeast (spanCodes [290, 162, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(290, 33), (162, 35), (19, 119), (10, 462), (6, 1)]
    (codeMat 481) (codeMat 115) (codeMat 492) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0201 :
    QuotientRankAtLeast (spanCodes [288, 160, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 32), (160, 34), (19, 119), (10, 441), (6, 1)]
    (codeMat 417) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0202 :
    QuotientRankAtLeast (spanCodes [354, 226, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(354, 494), (226, 492), (19, 441), (10, 462), (6, 1)]
    (codeMat 417) (codeMat 501) (codeMat 494) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0203 :
    QuotientRankAtLeast (spanCodes [353, 225, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(353, 408), (225, 410), (19, 462), (10, 441), (6, 1)]
    (codeMat 481) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0204 :
    QuotientRankAtLeast (spanCodes [256, 129, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(256, 16), (129, 53), (19, 245), (10, 350), (7, 36)]
    (codeMat 485) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0205 :
    QuotientRankAtLeast (spanCodes [320, 193, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(320, 16), (193, 53), (19, 427), (10, 350), (7, 36)]
    (codeMat 421) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0206 :
    QuotientRankAtLeast (spanCodes [288, 162, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 2), (162, 35), (19, 119), (10, 462), (4, 1)]
    (codeMat 369) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0207 :
    QuotientRankAtLeast (spanCodes [320, 194, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(320, 16), (194, 53), (19, 350), (10, 427), (4, 36)]
    (codeMat 485) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0208 :
    QuotientRankAtLeast (spanCodes [256, 131, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(256, 16), (131, 53), (19, 245), (10, 427), (5, 36)]
    (codeMat 421) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0209 :
    QuotientRankAtLeast (spanCodes [354, 225, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(354, 443), (225, 410), (19, 462), (10, 441), (5, 1)]
    (codeMat 369) (codeMat 494) (codeMat 501) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
