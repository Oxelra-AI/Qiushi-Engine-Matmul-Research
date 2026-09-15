import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0140 :
    QuotientRankAtLeast (spanCodes [275, 83, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 99), (83, 96), (34, 306), (10, 304)]
    (codeMat 214) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0141 :
    QuotientRankAtLeast (spanCodes [263, 65, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(263, 280), (65, 16), (39, 259), (20, 326), (10, 258)]
    (codeMat 107) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0142 :
    QuotientRankAtLeast (spanCodes [275, 66, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 305), (66, 338), (54, 1), (10, 322)]
    (codeMat 115) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane490GenSource0143 :
    QuotientRankAtLeast (spanCodes [275, 67, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 307), (67, 338), (55, 304), (10, 336)]
    (codeMat 87) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0144 :
    QuotientRankAtLeast (spanCodes [275, 83, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 339), (83, 336), (39, 306), (10, 304)]
    (codeMat 159) (codeMat 340) (codeMat 85) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0145 :
    QuotientRankAtLeast (spanCodes [275, 113, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(275, 369), (113, 96), (10, 274), (5, 2)]
    (codeMat 143) (codeMat 342) (codeMat 215) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane490GenSource0146 :
    QuotientRankAtLeast (spanCodes [262, 65, 34, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(262, 280), (65, 16), (34, 259), (21, 68), (10, 258)]
    (codeMat 106) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0147 :
    QuotientRankAtLeast (spanCodes [273, 128, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(273, 84), (128, 1), (8, 32), (2, 2)]
    (codeMat 140) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0148 :
    QuotientRankAtLeast (spanCodes [257, 128, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(257, 118), (128, 1), (18, 2), (10, 34)]
    (codeMat 156) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0149 :
    QuotientRankAtLeast (spanCodes [260, 130, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(260, 3), (130, 2), (23, 336), (10, 304)]
    (codeMat 93) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
