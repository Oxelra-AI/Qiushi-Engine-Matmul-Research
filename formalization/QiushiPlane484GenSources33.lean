import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0330 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 100), (128, 9), (64, 8), (18, 54), (10, 52), (1, 32)]
    (codeMat 84) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0331 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (132, 35), (68, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0332 :
    QuotientRankAtLeast (spanCodes [288, 166, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 3), (166, 35), (66, 440), (19, 119), (10, 441)]
    (codeMat 302) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0333 :
    QuotientRankAtLeast (spanCodes [292, 129, 97, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 3), (129, 440), (97, 35), (19, 441), (10, 119)]
    (codeMat 303) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0334 :
    QuotientRankAtLeast (spanCodes [288, 224, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 2), (224, 34), (19, 441), (10, 462), (4, 1)]
    (codeMat 305) (codeMat 213) (codeMat 470) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0335 :
    QuotientRankAtLeast (spanCodes [321, 129, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(321, 37), (129, 53), (19, 245), (10, 350), (4, 36)]
    (codeMat 485) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0336 :
    QuotientRankAtLeast (spanCodes [386, 66, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(386, 37), (66, 53), (19, 350), (10, 245), (4, 36)]
    (codeMat 421) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0337 :
    QuotientRankAtLeast (spanCodes [289, 162, 67, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 26), (162, 362), (67, 112), (19, 463), (10, 113), (4, 16)]
    (codeMat 271) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0338 :
    QuotientRankAtLeast (spanCodes [259, 163, 96, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 26), (163, 181), (96, 180), (19, 463), (10, 446), (4, 16)]
    (codeMat 461) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0339 :
    QuotientRankAtLeast (spanCodes [290, 131, 97, 19, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(290, 10), (131, 112), (97, 378), (19, 113), (10, 463), (4, 16)]
    (codeMat 270) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
