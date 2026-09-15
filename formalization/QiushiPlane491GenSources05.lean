import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane468GenFinal
import QiushiPlane473GenFinal
import QiushiPlane475GenFinal
import QiushiPlane477GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0050 :
    QuotientRankAtLeast (spanCodes [284, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(284, 240), (163, 250), (84, 84)]
    (codeMat 187) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0051 :
    QuotientRankAtLeast (spanCodes [285, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(285, 94), (163, 174), (84, 250)]
    (codeMat 494) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0052 :
    QuotientRankAtLeast (spanCodes [286, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [286, 163, 84] [(286, 163), (163, 330), (84, 445)]
    (codeMat 87) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane477Gen_lb18

theorem plane491GenSource0053 :
    QuotientRankAtLeast (spanCodes [287, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(287, 10), (163, 379), (84, 84)]
    (codeMat 110) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0054 :
    QuotientRankAtLeast (spanCodes [289, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(289, 240), (163, 250), (84, 84)]
    (codeMat 460) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0055 :
    QuotientRankAtLeast (spanCodes [290, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(290, 96), (163, 165), (84, 207)]
    (codeMat 117) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0056 :
    QuotientRankAtLeast (spanCodes [294, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(294, 293), (163, 303), (84, 379)]
    (codeMat 169) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0057 :
    QuotientRankAtLeast (spanCodes [295, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(295, 197), (163, 207), (84, 106)]
    (codeMat 172) (codeMat 93) (codeMat 372) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0058 :
    QuotientRankAtLeast (spanCodes [296, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(296, 10), (163, 369), (84, 94)]
    (codeMat 98) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0059 :
    QuotientRankAtLeast (spanCodes [297, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(297, 10), (163, 94), (84, 303)]
    (codeMat 117) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

end QiushiMatmul
