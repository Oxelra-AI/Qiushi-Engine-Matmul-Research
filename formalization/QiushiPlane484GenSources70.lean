import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0700 :
    QuotientRankAtLeast (spanCodes [417, 64, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(417, 379), (64, 192), (19, 350), (10, 245), (4, 36)]
    (codeMat 311) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0701 :
    QuotientRankAtLeast (spanCodes [291, 160, 97, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(291, 11), (160, 363), (97, 283), (19, 446), (10, 463), (7, 16)]
    (codeMat 334) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0702 :
    QuotientRankAtLeast (spanCodes [288, 162, 96, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(288, 27), (162, 363), (96, 283), (19, 446), (10, 463), (7, 16)]
    (codeMat 271) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0703 :
    QuotientRankAtLeast (spanCodes [288, 161, 99, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(288, 27), (161, 267), (99, 379), (19, 463), (10, 446), (7, 16)]
    (codeMat 335) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0704 :
    QuotientRankAtLeast (spanCodes [291, 163, 98, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(291, 11), (163, 267), (98, 379), (19, 463), (10, 446), (7, 16)]
    (codeMat 270) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0705 :
    QuotientRankAtLeast (spanCodes [256, 130, 97, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 27), (130, 1), (97, 196), (19, 113), (10, 463), (6, 16)]
    (codeMat 461) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0706 :
    QuotientRankAtLeast (spanCodes [288, 163, 96, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(288, 256), (163, 282), (96, 283), (19, 446), (10, 463), (6, 16)]
    (codeMat 397) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0707 :
    QuotientRankAtLeast (spanCodes [294, 128, 66, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(294, 100), (128, 63), (66, 28), (18, 54), (10, 52), (1, 32)]
    (codeMat 87) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0708 :
    QuotientRankAtLeast (spanCodes [450, 32, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(450, 112), (32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0709 :
    QuotientRankAtLeast (spanCodes [294, 166, 102, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(294, 495), (166, 493), (102, 492), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
