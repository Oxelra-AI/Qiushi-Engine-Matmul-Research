import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0610 :
    QuotientRankAtLeast (spanCodes [391, 64, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(391, 208), (64, 192), (36, 36), (19, 245), (10, 427)]
    (codeMat 302) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane484GenSource0611 :
    QuotientRankAtLeast (spanCodes [262, 134, 71, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 420), (134, 164), (71, 283), (36, 16), (19, 463), (10, 113)]
    (codeMat 286) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0612 :
    QuotientRankAtLeast (spanCodes [257, 128, 70, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 453), (128, 1), (70, 196), (36, 16), (19, 463), (10, 446)]
    (codeMat 348) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0613 :
    QuotientRankAtLeast (spanCodes [262, 132, 69, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 469), (132, 378), (69, 180), (36, 16), (19, 446), (10, 113)]
    (codeMat 478) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane484GenSource0614 :
    QuotientRankAtLeast (spanCodes [289, 128, 65, 16, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(289, 100), (128, 3), (65, 63), (16, 2), (9, 54), (3, 32)]
    (codeMat 86) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0615 :
    QuotientRankAtLeast (spanCodes [290, 130, 66, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(290, 100), (130, 63), (66, 60), (18, 54), (10, 52), (1, 32)]
    (codeMat 86) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane484GenSource0616 :
    QuotientRankAtLeast (spanCodes [292, 164, 100, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 32), (164, 35), (100, 34), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0617 :
    QuotientRankAtLeast (spanCodes [288, 131, 71, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 3), (131, 118), (71, 493), (19, 119), (10, 462)]
    (codeMat 318) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0618 :
    QuotientRankAtLeast (spanCodes [260, 161, 65, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 3), (161, 410), (65, 1), (19, 441), (10, 462)]
    (codeMat 317) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0619 :
    QuotientRankAtLeast (spanCodes [260, 196, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 2), (196, 34), (36, 1), (19, 462), (10, 119)]
    (codeMat 299) (codeMat 213) (codeMat 470) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
