import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiWcOrbit141Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0180 :
    QuotientRankAtLeast (spanCodes [386, 66, 48, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(386, 88), (66, 90), (48, 32), (10, 108), (6, 8), (1, 9)]
    (codeMat 161) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane486GenSource0181 :
    QuotientRankAtLeast (spanCodes [384, 66, 50, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(384, 2), (66, 83), (50, 69), (10, 101), (6, 1), (1, 9)]
    (codeMat 161) (codeMat 395) (codeMat 474) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane486GenSource0182 :
    QuotientRankAtLeast (spanCodes [279, 144, 68, 49, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(279, 299), (144, 2), (68, 350), (49, 265), (10, 383)]
    (codeMat 254) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane486GenSource0183 :
    QuotientRankAtLeast (spanCodes [290, 146, 66, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(290, 41), (146, 40), (66, 175), (10, 173), (6, 9)]
    (codeMat 190) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0184 :
    QuotientRankAtLeast (spanCodes [291, 147, 66, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(291, 43), (147, 42), (66, 175), (10, 173), (6, 9)]
    (codeMat 254) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0185 :
    QuotientRankAtLeast (spanCodes [386, 66, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(386, 135), (66, 175), (50, 134), (10, 166), (6, 2)]
    (codeMat 142) (codeMat 395) (codeMat 474) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0186 :
    QuotientRankAtLeast (spanCodes [289, 144, 67, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(289, 34), (144, 40), (67, 175), (10, 173), (7, 9)]
    (codeMat 183) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0187 :
    QuotientRankAtLeast (spanCodes [288, 145, 67, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(288, 32), (145, 42), (67, 175), (10, 173), (7, 9)]
    (codeMat 247) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0188 :
    QuotientRankAtLeast (spanCodes [274, 144, 67, 51, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 119), (144, 130), (67, 235), (51, 255), (10, 227), (7, 3)]
    (codeMat 183) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0189 :
    QuotientRankAtLeast (spanCodes [385, 67, 48, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(385, 42), (67, 173), (48, 32), (10, 164), (7, 2)]
    (codeMat 143) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
