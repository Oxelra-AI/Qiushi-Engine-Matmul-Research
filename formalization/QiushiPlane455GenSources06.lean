import QiushiPlane455GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane455GenSource0060 :
    QuotientRankAtLeast (spanCodes [263, 129, 71, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 252), (129, 245), (71, 126), (34, 104), (20, 96), (10, 232)]
    (codeMat 158) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane455GenSource0061 :
    QuotientRankAtLeast (spanCodes [263, 129, 66, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 96), (129, 105), (66, 97), (39, 224), (20, 255), (10, 227)]
    (codeMat 117) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane455GenSource0062 :
    QuotientRankAtLeast (spanCodes [257, 129, 67, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 223), (129, 222), (67, 437), (33, 479), (20, 97), (10, 430)]
    (codeMat 412) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane455GenSource0063 :
    QuotientRankAtLeast (spanCodes [257, 129, 71, 37, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 20), (129, 420), (71, 180), (37, 21), (20, 367), (10, 191)]
    (codeMat 335) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane455GenSource0064 :
    QuotientRankAtLeast (spanCodes [256, 129, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 27), (129, 420), (96, 238), (17, 160), (10, 176), (5, 320)]
    (codeMat 95) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane455GenSource0065 :
    QuotientRankAtLeast (spanCodes [259, 129, 97, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 272), (129, 112), (97, 196), (19, 113), (10, 463), (7, 16)]
    (codeMat 335) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane455GenSource0066 :
    QuotientRankAtLeast (spanCodes [257, 129, 99, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 368), (129, 112), (99, 213), (19, 113), (10, 446), (7, 16)]
    (codeMat 271) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane455GenSource0067 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(260, 1), (129, 197), (68, 257), (38, 463), (20, 113), (10, 430)]
    (codeMat 277) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane455GenSource0068 :
    QuotientRankAtLeast (spanCodes [260, 129, 69, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 432), (129, 367), (69, 222), (39, 127), (20, 420), (10, 191)]
    (codeMat 244) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane455GenSource0069 :
    QuotientRankAtLeast (spanCodes [292, 129, 67, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 3), (129, 441), (67, 119), (20, 411), (10, 118)]
    (codeMat 183) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
