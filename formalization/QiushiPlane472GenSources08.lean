import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0080 :
    QuotientRankAtLeast (spanCodes [273, 144, 82, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(273, 171), (144, 1), (82, 447), (51, 160), (10, 496), (6, 16)]
    (codeMat 206) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane472GenSource0081 :
    QuotientRankAtLeast (spanCodes [272, 145, 82, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(272, 97), (145, 197), (82, 222), (50, 352), (10, 368), (6, 256)]
    (codeMat 87) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane472GenSource0082 :
    QuotientRankAtLeast (spanCodes [275, 145, 82, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(275, 394), (145, 452), (82, 228), (49, 11), (10, 31), (6, 1)]
    (codeMat 465) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane472GenSource0083 :
    QuotientRankAtLeast (spanCodes [288, 164, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 1), (164, 126), (84, 84), (8, 32), (2, 384)]
    (codeMat 86) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane472GenSource0084 :
    QuotientRankAtLeast (spanCodes [273, 145, 81, 51, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(273, 254), (145, 255), (81, 252), (51, 136), (10, 224), (5, 128)]
    (codeMat 92) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0085 :
    QuotientRankAtLeast (spanCodes [256, 146, 84, 34, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(256, 1), (146, 32), (84, 335), (34, 356), (10, 164)]
    (codeMat 188) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane472GenSource0086 :
    QuotientRankAtLeast (spanCodes [257, 130, 69, 35, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 222), (130, 1), (69, 437), (35, 272), (17, 352), (10, 96)]
    (codeMat 213) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane472GenSource0087 :
    QuotientRankAtLeast (spanCodes [262, 133, 69, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 224), (133, 252), (69, 255), (36, 128), (17, 148), (10, 150)]
    (codeMat 95) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0088 :
    QuotientRankAtLeast (spanCodes [261, 134, 69, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 104), (134, 224), (69, 96), (39, 148), (17, 151), (10, 149)]
    (codeMat 355) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0089 :
    QuotientRankAtLeast (spanCodes [263, 129, 64, 37, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(263, 464), (129, 240), (64, 384), (37, 463), (20, 251), (10, 414)]
    (codeMat 270) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

end QiushiMatmul
