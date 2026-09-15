import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane152GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0190 :
    QuotientRankAtLeast (spanCodes [310, 151, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(310, 323), (151, 289), (84, 305), (10, 338)]
    (codeMat 239) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0191 :
    QuotientRankAtLeast (spanCodes [390, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(390, 288), (84, 305), (39, 322), (10, 323)]
    (codeMat 187) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0192 :
    QuotientRankAtLeast (spanCodes [404, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(404, 338), (84, 337), (53, 304), (10, 306)]
    (codeMat 159) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0193 :
    QuotientRankAtLeast (spanCodes [305, 146, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(305, 95), (146, 1), (83, 332), (10, 264), (7, 16)]
    (codeMat 143) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0194 :
    QuotientRankAtLeast (spanCodes [291, 129, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(291, 11), (129, 333), (83, 68), (10, 264), (7, 16)]
    (codeMat 206) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0195 :
    QuotientRankAtLeast (spanCodes [292, 130, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(292, 288), (130, 16), (84, 99), (10, 338)]
    (codeMat 174) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0196 :
    QuotientRankAtLeast (spanCodes [310, 144, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(310, 306), (144, 2), (84, 99), (10, 338)]
    (codeMat 174) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0197 :
    QuotientRankAtLeast (spanCodes [390, 84, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(390, 288), (84, 114), (32, 1), (10, 323)]
    (codeMat 242) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0198 :
    QuotientRankAtLeast (spanCodes [404, 84, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(404, 96), (84, 99), (50, 304), (10, 306)]
    (codeMat 214) (codeMat 241) (codeMat 489) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0199 :
    QuotientRankAtLeast (spanCodes [261, 148, 84, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 96, 16, 10, 1] [(261, 197), (148, 191), (84, 190), (54, 16), (10, 112)]
    (codeMat 92) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane152Gen_lb16

end QiushiMatmul
