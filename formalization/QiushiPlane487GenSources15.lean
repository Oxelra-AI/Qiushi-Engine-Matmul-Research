import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane275GenFinal
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0150 :
    QuotientRankAtLeast (spanCodes [256, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(256, 1), (64, 2), (20, 96), (10, 272)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane487GenSource0151 :
    QuotientRankAtLeast (spanCodes [260, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 2, 1] [(260, 1), (84, 244), (36, 2), (10, 160)]
    (codeMat 93) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane275Gen_lb16

theorem plane487GenSource0152 :
    QuotientRankAtLeast (spanCodes [256, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(256, 1), (84, 99), (36, 2), (10, 306)]
    (codeMat 156) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0153 :
    QuotientRankAtLeast (spanCodes [260, 84, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(260, 1), (84, 337), (32, 2), (10, 306)]
    (codeMat 213) (codeMat 213) (codeMat 470) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0154 :
    QuotientRankAtLeast (spanCodes [273, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(273, 98), (84, 114), (53, 322), (10, 323)]
    (codeMat 171) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0155 :
    QuotientRankAtLeast (spanCodes [276, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(276, 289), (84, 305), (48, 1), (10, 323)]
    (codeMat 226) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0156 :
    QuotientRankAtLeast (spanCodes [288, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(288, 2), (80, 304), (10, 96), (4, 1)]
    (codeMat 177) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0157 :
    QuotientRankAtLeast (spanCodes [259, 64, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(259, 280), (64, 16), (39, 259), (20, 326), (10, 258)]
    (codeMat 99) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0158 :
    QuotientRankAtLeast (spanCodes [262, 65, 34, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(262, 280), (65, 16), (34, 259), (21, 68), (10, 258)]
    (codeMat 106) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0159 :
    QuotientRankAtLeast (spanCodes [292, 67, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(292, 3), (67, 97), (23, 304), (10, 96)]
    (codeMat 143) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
