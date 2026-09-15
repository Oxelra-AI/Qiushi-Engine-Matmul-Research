import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0040 :
    QuotientRankAtLeast (spanCodes [275, 145, 67, 51, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(275, 99), (145, 139), (67, 245), (51, 227), (10, 252), (7, 3)]
    (codeMat 183) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0041 :
    QuotientRankAtLeast (spanCodes [274, 145, 66, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 118), (145, 31), (66, 227), (51, 104), (10, 224), (6, 8)]
    (codeMat 206) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0042 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 11), (129, 139), (65, 9), (35, 227), (10, 252), (5, 3)]
    (codeMat 165) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (129, 30), (64, 3), (35, 96), (10, 232), (4, 8)]
    (codeMat 204) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0044 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (130, 128), (68, 104), (32, 1), (16, 2), (10, 148)]
    (codeMat 354) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 31), (128, 3), (68, 252), (34, 22), (16, 2), (10, 148)]
    (codeMat 86) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0046 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 96), (130, 1), (68, 104), (32, 128), (16, 2), (10, 148)]
    (codeMat 85) (codeMat 330) (codeMat 394) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0047 :
    QuotientRankAtLeast (spanCodes [259, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 104), (128, 128), (68, 224), (34, 148), (16, 2), (10, 151)]
    (codeMat 298) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0048 :
    QuotientRankAtLeast (spanCodes [261, 134, 68, 36, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 378), (134, 180), (68, 469), (36, 16), (16, 256), (10, 96)]
    (codeMat 158) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane461GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 150, 68, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (150, 446), (68, 26), (52, 496), (10, 160), (1, 16)]
    (codeMat 205) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
