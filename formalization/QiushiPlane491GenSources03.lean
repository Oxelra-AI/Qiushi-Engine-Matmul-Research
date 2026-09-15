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

theorem plane491GenSource0030 :
    QuotientRankAtLeast (spanCodes [257, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(257, 96), (163, 165), (84, 207)]
    (codeMat 124) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0031 :
    QuotientRankAtLeast (spanCodes [258, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(258, 10), (163, 169), (84, 84)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

theorem plane491GenSource0032 :
    QuotientRankAtLeast (spanCodes [259, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(259, 164), (163, 84), (84, 174)]
    (codeMat 307) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0033 :
    QuotientRankAtLeast (spanCodes [261, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(261, 293), (163, 303), (84, 379)]
    (codeMat 253) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0034 :
    QuotientRankAtLeast (spanCodes [262, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(262, 10), (163, 84), (84, 174)]
    (codeMat 233) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0035 :
    QuotientRankAtLeast (spanCodes [263, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(263, 96), (163, 372), (84, 286)]
    (codeMat 98) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0036 :
    QuotientRankAtLeast (spanCodes [265, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(265, 276), (163, 106), (84, 372)]
    (codeMat 190) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0037 :
    QuotientRankAtLeast (spanCodes [266, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(266, 84), (163, 303), (84, 369)]
    (codeMat 190) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0038 :
    QuotientRankAtLeast (spanCodes [267, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(267, 84), (163, 94), (84, 303)]
    (codeMat 214) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0039 :
    QuotientRankAtLeast (spanCodes [268, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(268, 10), (163, 84), (84, 174)]
    (codeMat 445) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

end QiushiMatmul
