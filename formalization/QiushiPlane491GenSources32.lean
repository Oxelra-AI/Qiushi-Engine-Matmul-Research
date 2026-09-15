import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0320 :
    QuotientRankAtLeast (spanCodes [260, 131, 65, 32, 21, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 1), (131, 150), (65, 2), (32, 8), (21, 232), (9, 128)]
    (codeMat 213) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0321 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 38, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 180), (133, 272), (65, 260), (38, 191), (21, 464), (10, 453)]
    (codeMat 335) (codeMat 229) (codeMat 187) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane491GenSource0322 :
    QuotientRankAtLeast (spanCodes [257, 135, 67, 36, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 436), (135, 437), (67, 223), (36, 16), (23, 430), (10, 479)]
    (codeMat 477) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0323 :
    QuotientRankAtLeast (spanCodes [256, 131, 71, 32, 19, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (131, 224), (71, 252), (32, 1), (19, 96), (11, 104)]
    (codeMat 114) (codeMat 204) (codeMat 114) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0324 :
    QuotientRankAtLeast (spanCodes [260, 135, 71, 36, 19, 11]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 130), (135, 252), (71, 245), (36, 128), (19, 104), (11, 96)]
    (codeMat 214) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0325 :
    QuotientRankAtLeast (spanCodes [258, 133, 68, 38, 16, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 453), (133, 170), (68, 464), (38, 261), (16, 260), (12, 96)]
    (codeMat 163) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane491GenSource0326 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 35, 20, 12]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 20), (128, 128), (64, 130), (35, 28), (20, 224), (12, 227)]
    (codeMat 102) (codeMat 225) (codeMat 169) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0327 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 39, 16, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (132, 96), (68, 105), (39, 20), (16, 128), (15, 150)]
    (codeMat 84) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0328 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 34, 20, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 104), (129, 105), (64, 8), (34, 148), (20, 150), (15, 20)]
    (codeMat 92) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0329 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 23, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 3), (131, 68), (67, 69), (32, 24), (23, 160), (15, 168)]
    (codeMat 84) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
