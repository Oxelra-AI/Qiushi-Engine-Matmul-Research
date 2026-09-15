import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0260 :
    QuotientRankAtLeast (spanCodes [325, 192, 32, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(325, 16), (192, 192), (32, 36), (19, 245), (10, 350)]
    (codeMat 303) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0261 :
    QuotientRankAtLeast (spanCodes [259, 133, 35, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(259, 495), (133, 493), (35, 463), (19, 462), (10, 119)]
    (codeMat 426) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0262 :
    QuotientRankAtLeast (spanCodes [256, 134, 35, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 32), (134, 34), (35, 440), (19, 441), (10, 119)]
    (codeMat 298) (codeMat 115) (codeMat 492) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0263 :
    QuotientRankAtLeast (spanCodes [321, 199, 35, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(321, 495), (199, 493), (35, 118), (19, 119), (10, 441)]
    (codeMat 426) (codeMat 501) (codeMat 494) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0264 :
    QuotientRankAtLeast (spanCodes [320, 198, 35, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(320, 32), (198, 34), (35, 118), (19, 119), (10, 462)]
    (codeMat 298) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0265 :
    QuotientRankAtLeast (spanCodes [260, 131, 34, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(260, 16), (131, 414), (34, 209), (19, 350), (10, 245)]
    (codeMat 431) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0266 :
    QuotientRankAtLeast (spanCodes [320, 199, 34, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(320, 2), (199, 493), (34, 440), (19, 119), (10, 441)]
    (codeMat 482) (codeMat 465) (codeMat 465) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0267 :
    QuotientRankAtLeast (spanCodes [288, 128, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(288, 16), (128, 192), (19, 245), (10, 427), (5, 36)]
    (codeMat 311) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0268 :
    QuotientRankAtLeast (spanCodes [320, 224, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(320, 2), (224, 493), (19, 462), (10, 441), (5, 1)]
    (codeMat 481) (codeMat 494) (codeMat 501) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0269 :
    QuotientRankAtLeast (spanCodes [256, 161, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (161, 84), (19, 119), (10, 462), (4, 1)]
    (codeMat 481) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
