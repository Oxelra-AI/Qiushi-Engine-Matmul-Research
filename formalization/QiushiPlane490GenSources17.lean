import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane298GenFinal
import QiushiPlane336GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0170 :
    QuotientRankAtLeast (spanCodes [275, 144, 67, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 395), (144, 32), (67, 43), (10, 42)]
    (codeMat 407) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0171 :
    QuotientRankAtLeast (spanCodes [275, 146, 65, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 417), (146, 1), (65, 32), (10, 42)]
    (codeMat 335) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0172 :
    QuotientRankAtLeast (spanCodes [275, 149, 65, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(275, 369), (149, 368), (65, 2), (10, 274)]
    (codeMat 117) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane490GenSource0173 :
    QuotientRankAtLeast (spanCodes [275, 165, 113, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(275, 98), (165, 99), (113, 257), (10, 371)]
    (codeMat 375) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane490GenSource0174 :
    QuotientRankAtLeast (spanCodes [260, 195, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(260, 3), (195, 2), (23, 96), (10, 304)]
    (codeMat 85) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0175 :
    QuotientRankAtLeast (spanCodes [275, 210, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 115), (210, 338), (10, 322), (6, 1)]
    (codeMat 241) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane490GenSource0176 :
    QuotientRankAtLeast (spanCodes [275, 211, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 99), (211, 96), (10, 304), (7, 2)]
    (codeMat 141) (codeMat 348) (codeMat 125) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0177 :
    QuotientRankAtLeast (spanCodes [275, 130, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(275, 94), (130, 1), (81, 68), (10, 264), (5, 16)]
    (codeMat 141) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0178 :
    QuotientRankAtLeast (spanCodes [275, 144, 113, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(275, 99), (144, 2), (113, 368), (10, 274)]
    (codeMat 174) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane490GenSource0179 :
    QuotientRankAtLeast (spanCodes [275, 149, 116, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(275, 273), (149, 17), (116, 114), (10, 371)]
    (codeMat 382) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

end QiushiMatmul
