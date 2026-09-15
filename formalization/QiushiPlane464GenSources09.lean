import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0090 :
    QuotientRankAtLeast (spanCodes [262, 129, 68, 34, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 21), (129, 191), (68, 367), (34, 20), (23, 180), (10, 420)]
    (codeMat 207) (codeMat 95) (codeMat 244) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0091 :
    QuotientRankAtLeast (spanCodes [260, 131, 68, 33, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 432), (131, 420), (68, 180), (33, 378), (22, 367), (10, 191)]
    (codeMat 270) (codeMat 443) (codeMat 254) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0092 :
    QuotientRankAtLeast (spanCodes [259, 132, 68, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(259, 11), (132, 20), (68, 21), (38, 180), (22, 404), (10, 462)]
    (codeMat 492) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane464GenSource0093 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 1), (68, 148), (36, 128), (16, 8), (10, 104)]
    (codeMat 212) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0094 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 38, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 260), (133, 272), (68, 180), (38, 453), (23, 464), (10, 191)]
    (codeMat 334) (codeMat 397) (codeMat 250) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0095 :
    QuotientRankAtLeast (spanCodes [263, 134, 68, 36, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 378), (134, 464), (68, 367), (36, 432), (22, 272), (10, 420)]
    (codeMat 143) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0096 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 35, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 222), (132, 362), (68, 363), (35, 97), (19, 113), (10, 463)]
    (codeMat 468) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane464GenSource0097 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (133, 245), (68, 287), (35, 176), (18, 320), (10, 336)]
    (codeMat 214) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane464GenSource0098 :
    QuotientRankAtLeast (spanCodes [304, 176, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 96), (176, 104), (64, 1), (10, 148), (4, 128), (1, 2)]
    (codeMat 140) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0099 :
    QuotientRankAtLeast (spanCodes [306, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(306, 127), (178, 119), (66, 23), (10, 151), (6, 1), (1, 2)]
    (codeMat 417) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
