import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane275GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0170 :
    QuotientRankAtLeast (spanCodes [273, 151, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(273, 98), (151, 97), (84, 99), (10, 338)]
    (codeMat 253) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0171 :
    QuotientRankAtLeast (spanCodes [276, 146, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(276, 304), (146, 16), (84, 305), (10, 338)]
    (codeMat 188) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0172 :
    QuotientRankAtLeast (spanCodes [384, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(384, 2), (82, 336), (10, 96), (6, 1)]
    (codeMat 161) (codeMat 396) (codeMat 106) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0173 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 10), (128, 1), (80, 68), (10, 264), (4, 16)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0174 :
    QuotientRankAtLeast (spanCodes [274, 145, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(274, 326), (145, 333), (81, 332), (10, 264), (5, 16)]
    (codeMat 204) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0175 :
    QuotientRankAtLeast (spanCodes [273, 130, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 2, 1] [(273, 85), (130, 2), (84, 84), (10, 160)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane275Gen_lb16

theorem plane487GenSource0176 :
    QuotientRankAtLeast (spanCodes [390, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(390, 3), (65, 1), (21, 304), (10, 96)]
    (codeMat 141) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0177 :
    QuotientRankAtLeast (spanCodes [256, 148, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(256, 1), (148, 97), (84, 99), (10, 338)]
    (codeMat 244) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0178 :
    QuotientRankAtLeast (spanCodes [260, 144, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(260, 1), (144, 16), (84, 305), (10, 338)]
    (codeMat 181) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0179 :
    QuotientRankAtLeast (spanCodes [273, 133, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(273, 98), (133, 289), (84, 99), (10, 338)]
    (codeMat 253) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

end QiushiMatmul
