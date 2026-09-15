import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit231Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0410 :
    QuotientRankAtLeast (spanCodes [256, 165, 98, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(256, 256), (165, 396), (98, 156), (19, 371), (10, 413)]
    (codeMat 302) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane484GenSource0411 :
    QuotientRankAtLeast (spanCodes [260, 161, 98, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 2), (161, 85), (98, 84), (19, 119), (10, 441)]
    (codeMat 317) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0412 :
    QuotientRankAtLeast (spanCodes [288, 224, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 32), (224, 34), (19, 441), (10, 462), (7, 1)]
    (codeMat 417) (codeMat 241) (codeMat 489) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0413 :
    QuotientRankAtLeast (spanCodes [354, 162, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(354, 409), (162, 411), (19, 119), (10, 441), (7, 1)]
    (codeMat 417) (codeMat 346) (codeMat 459) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0414 :
    QuotientRankAtLeast (spanCodes [352, 160, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(352, 495), (160, 493), (19, 119), (10, 462), (7, 1)]
    (codeMat 481) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0415 :
    QuotientRankAtLeast (spanCodes [419, 99, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(419, 494), (99, 492), (19, 462), (10, 119), (7, 1)]
    (codeMat 417) (codeMat 431) (codeMat 477) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0416 :
    QuotientRankAtLeast (spanCodes [418, 98, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(418, 408), (98, 410), (19, 441), (10, 119), (7, 1)]
    (codeMat 481) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0417 :
    QuotientRankAtLeast (spanCodes [256, 193, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(256, 16), (193, 53), (19, 427), (10, 350), (6, 36)]
    (codeMat 421) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0418 :
    QuotientRankAtLeast (spanCodes [320, 129, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(320, 16), (129, 53), (19, 245), (10, 350), (6, 36)]
    (codeMat 485) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0419 :
    QuotientRankAtLeast (spanCodes [288, 161, 64, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(288, 256), (161, 266), (64, 1), (19, 446), (10, 113), (6, 16)]
    (codeMat 396) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
