import QiushiPlane474GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit220Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane474GenSource0050 :
    QuotientRankAtLeast (spanCodes [257, 80, 32, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 22), (80, 252), (32, 3), (9, 9), (4, 2), (3, 130)]
    (codeMat 267) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0051 :
    QuotientRankAtLeast (spanCodes [256, 80, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (80, 224), (34, 20), (10, 28), (4, 2), (1, 3)]
    (codeMat 273) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0052 :
    QuotientRankAtLeast (spanCodes [294, 134, 66, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(294, 136), (134, 232), (66, 29), (22, 224), (10, 28), (1, 3)]
    (codeMat 190) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0053 :
    QuotientRankAtLeast (spanCodes [293, 133, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(293, 22), (133, 227), (64, 130), (20, 232), (9, 128), (3, 8)]
    (codeMat 207) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0054 :
    QuotientRankAtLeast (spanCodes [292, 160, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(292, 1), (160, 209), (84, 379), (8, 36), (2, 192)]
    (codeMat 111) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane474GenSource0055 :
    QuotientRankAtLeast (spanCodes [259, 129, 83, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 452), (129, 31), (83, 10), (34, 420), (10, 20), (7, 260)]
    (codeMat 94) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane474GenSource0056 :
    QuotientRankAtLeast (spanCodes [274, 144, 83, 51, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 97), (144, 1), (83, 433), (51, 420), (10, 127), (7, 192)]
    (codeMat 102) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane474GenSource0057 :
    QuotientRankAtLeast (spanCodes [273, 146, 82, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 270), (146, 260), (82, 276), (49, 78), (10, 436), (6, 1)]
    (codeMat 417) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane474GenSource0058 :
    QuotientRankAtLeast (spanCodes [288, 160, 82, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(288, 32), (160, 33), (82, 118), (10, 383), (6, 2)]
    (codeMat 396) (codeMat 123) (codeMat 236) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane474GenSource0059 :
    QuotientRankAtLeast (spanCodes [259, 131, 83, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 452), (131, 453), (83, 170), (34, 96), (10, 464), (7, 192)]
    (codeMat 92) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
