import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0260 :
    QuotientRankAtLeast (spanCodes [259, 195, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(259, 34), (195, 32), (38, 441), (20, 119), (10, 463)]
    (codeMat 354) (codeMat 239) (codeMat 351) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane485GenSource0261 :
    QuotientRankAtLeast (spanCodes [387, 67, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(387, 493), (67, 495), (38, 119), (20, 441), (10, 463)]
    (codeMat 482) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane485GenSource0262 :
    QuotientRankAtLeast (spanCodes [258, 132, 71, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 104), (132, 96), (71, 105), (39, 252), (20, 224), (10, 255)]
    (codeMat 117) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0263 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 437), (129, 79), (64, 1), (36, 320), (20, 336), (10, 496)]
    (codeMat 212) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0264 :
    QuotientRankAtLeast (spanCodes [262, 131, 65, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 436), (131, 78), (65, 1), (34, 176), (20, 160), (10, 496)]
    (codeMat 157) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0265 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (128, 9), (70, 104), (32, 3), (20, 31), (10, 252)]
    (codeMat 116) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0266 :
    QuotientRankAtLeast (spanCodes [262, 131, 67, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 496), (131, 160), (67, 176), (32, 1), (20, 78), (10, 436)]
    (codeMat 354) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0267 :
    QuotientRankAtLeast (spanCodes [262, 129, 65, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 496), (129, 336), (65, 16), (32, 1), (20, 79), (10, 506)]
    (codeMat 298) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0268 :
    QuotientRankAtLeast (spanCodes [261, 194, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(261, 495), (194, 493), (33, 463), (20, 440), (10, 118)]
    (codeMat 491) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane485GenSource0269 :
    QuotientRankAtLeast (spanCodes [256, 225, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 32), (225, 85), (19, 441), (10, 462), (7, 1)]
    (codeMat 305) (codeMat 241) (codeMat 489) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
