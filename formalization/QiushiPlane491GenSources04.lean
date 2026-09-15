import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane467GenFinal
import QiushiPlane468GenFinal
import QiushiPlane473GenFinal
import QiushiPlane475GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0040 :
    QuotientRankAtLeast (spanCodes [269, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(269, 96), (163, 372), (84, 286)]
    (codeMat 382) (codeMat 354) (codeMat 142) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0041 :
    QuotientRankAtLeast (spanCodes [270, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(270, 369), (163, 84), (84, 303)]
    (codeMat 183) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0042 :
    QuotientRankAtLeast (spanCodes [272, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(272, 197), (163, 207), (84, 106)]
    (codeMat 190) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0043 :
    QuotientRankAtLeast (spanCodes [274, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(274, 10), (163, 286), (84, 106)]
    (codeMat 124) (codeMat 111) (codeMat 412) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0044 :
    QuotientRankAtLeast (spanCodes [278, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(278, 240), (163, 250), (84, 84)]
    (codeMat 375) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0045 :
    QuotientRankAtLeast (spanCodes [279, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(279, 94), (163, 174), (84, 250)]
    (codeMat 114) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0046 :
    QuotientRankAtLeast (spanCodes [280, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(280, 10), (163, 84), (84, 174)]
    (codeMat 340) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0047 :
    QuotientRankAtLeast (spanCodes [281, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(281, 169), (163, 247), (84, 163)]
    (codeMat 87) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

theorem plane491GenSource0048 :
    QuotientRankAtLeast (spanCodes [282, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(282, 369), (163, 84), (84, 303)]
    (codeMat 123) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0049 :
    QuotientRankAtLeast (spanCodes [283, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(283, 293), (163, 303), (84, 379)]
    (codeMat 84) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

end QiushiMatmul
