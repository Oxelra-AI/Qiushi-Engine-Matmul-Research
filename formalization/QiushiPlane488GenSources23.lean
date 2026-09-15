import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0230 :
    QuotientRankAtLeast (spanCodes [263, 129, 70, 38, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 238), (129, 490), (70, 287), (38, 160), (18, 16), (10, 336)]
    (codeMat 159) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane488GenSource0231 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(256, 2), (128, 1), (66, 70), (34, 80), (16, 8), (10, 112)]
    (codeMat 84) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane488GenSource0232 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane488GenSource0233 :
    QuotientRankAtLeast (spanCodes [259, 135, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 28), (135, 252), (71, 255), (39, 20), (17, 148), (10, 150)]
    (codeMat 95) (codeMat 249) (codeMat 425) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0234 :
    QuotientRankAtLeast (spanCodes [256, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (135, 232), (68, 104), (36, 1), (17, 150), (10, 148)]
    (codeMat 355) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0235 :
    QuotientRankAtLeast (spanCodes [258, 135, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 232), (135, 96), (71, 224), (39, 150), (17, 149), (10, 151)]
    (codeMat 299) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0236 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 96), (135, 105), (68, 104), (36, 128), (17, 150), (10, 148)]
    (codeMat 93) (codeMat 474) (codeMat 395) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0237 :
    QuotientRankAtLeast (spanCodes [259, 134, 66, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 78), (134, 436), (66, 507), (34, 160), (20, 176), (10, 480)]
    (codeMat 157) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane488GenSource0238 :
    QuotientRankAtLeast (spanCodes [262, 150, 66, 34, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 227), (150, 28), (66, 105), (34, 224), (10, 96), (1, 8)]
    (codeMat 143) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0239 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 1), (68, 148), (36, 128), (16, 8), (10, 104)]
    (codeMat 212) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
