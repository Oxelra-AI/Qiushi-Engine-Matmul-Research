import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0240 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (64, 128), (32, 1), (16, 8), (10, 96)]
    (codeMat 98) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0241 :
    QuotientRankAtLeast (spanCodes [263, 130, 65, 33, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 104), (130, 1), (65, 9), (33, 252), (16, 3), (10, 31)]
    (codeMat 125) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0242 :
    QuotientRankAtLeast (spanCodes [261, 128, 67, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 252), (128, 130), (67, 139), (35, 104), (18, 128), (10, 136)]
    (codeMat 215) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0243 :
    QuotientRankAtLeast (spanCodes [256, 128, 80, 48, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 3), (80, 28), (48, 8), (10, 224), (4, 128)]
    (codeMat 84) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0244 :
    QuotientRankAtLeast (spanCodes [258, 144, 67, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 246), (144, 128), (67, 232), (35, 252), (10, 224), (5, 3)]
    (codeMat 183) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0245 :
    QuotientRankAtLeast (spanCodes [273, 146, 81, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 95), (146, 27), (81, 287), (49, 79), (10, 507), (6, 1)]
    (codeMat 305) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane488GenSource0246 :
    QuotientRankAtLeast (spanCodes [258, 133, 71, 39, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 252), (133, 139), (71, 126), (39, 104), (21, 136), (10, 232)]
    (codeMat 214) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0247 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (128, 8), (66, 97), (34, 224), (21, 28), (10, 227)]
    (codeMat 116) (codeMat 337) (codeMat 337) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0248 :
    QuotientRankAtLeast (spanCodes [258, 132, 71, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 104), (132, 96), (71, 105), (39, 252), (20, 224), (10, 255)]
    (codeMat 117) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0249 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 128), (68, 148), (36, 1), (17, 96), (10, 104)]
    (codeMat 99) (codeMat 204) (codeMat 114) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
