import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0240 :
    QuotientRankAtLeast (spanCodes [256, 135, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (135, 493), (36, 1), (19, 462), (10, 441)]
    (codeMat 419) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0241 :
    QuotientRankAtLeast (spanCodes [325, 194, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(325, 16), (194, 414), (36, 36), (19, 427), (10, 245)]
    (codeMat 494) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0242 :
    QuotientRankAtLeast (spanCodes [260, 132, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 2), (132, 34), (36, 1), (19, 441), (10, 462)]
    (codeMat 299) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0243 :
    QuotientRankAtLeast (spanCodes [323, 195, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(323, 208), (195, 192), (36, 36), (19, 350), (10, 245)]
    (codeMat 359) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0244 :
    QuotientRankAtLeast (spanCodes [262, 128, 34, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(262, 208), (128, 192), (34, 209), (19, 427), (10, 245)]
    (codeMat 303) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0245 :
    QuotientRankAtLeast (spanCodes [320, 198, 34, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(320, 2), (198, 34), (34, 463), (19, 119), (10, 462)]
    (codeMat 354) (codeMat 494) (codeMat 501) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0246 :
    QuotientRankAtLeast (spanCodes [291, 128, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(291, 37), (128, 192), (19, 245), (10, 427), (7, 36)]
    (codeMat 311) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0247 :
    QuotientRankAtLeast (spanCodes [352, 195, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(352, 398), (195, 192), (19, 350), (10, 427), (7, 36)]
    (codeMat 375) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0248 :
    QuotientRankAtLeast (spanCodes [261, 133, 37, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(261, 495), (133, 493), (37, 463), (19, 462), (10, 441)]
    (codeMat 419) (codeMat 115) (codeMat 492) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0249 :
    QuotientRankAtLeast (spanCodes [260, 132, 37, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (132, 34), (37, 440), (19, 441), (10, 462)]
    (codeMat 355) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
