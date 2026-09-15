import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
import QiushiPlane457GenFinal
import QiushiPlane458GenFinal
import QiushiPlane470GenFinal
import QiushiPlane472GenFinal
import QiushiPlane474GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0060 :
    QuotientRankAtLeast (spanCodes [258, 163, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 84, 10] [(258, 290), (163, 380), (10, 296)]
    (codeMat 212) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane472Gen_lb18

theorem plane489GenSource0061 :
    QuotientRankAtLeast (spanCodes [258, 164, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 30), (164, 20), (10, 96)]
    (codeMat 250) (codeMat 124) (codeMat 124) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0062 :
    QuotientRankAtLeast (spanCodes [258, 165, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 10), (165, 94), (10, 259)]
    (codeMat 169) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0063 :
    QuotientRankAtLeast (spanCodes [258, 166, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 20), (166, 10), (10, 476)]
    (codeMat 110) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0064 :
    QuotientRankAtLeast (spanCodes [258, 167, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(258, 10), (167, 94), (10, 294)]
    (codeMat 481) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane489GenSource0065 :
    QuotientRankAtLeast (spanCodes [258, 176, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 80), (176, 10), (10, 78)]
    (codeMat 354) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0066 :
    QuotientRankAtLeast (spanCodes [258, 177, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 265), (177, 94), (10, 10)]
    (codeMat 282) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0067 :
    QuotientRankAtLeast (spanCodes [258, 179, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(258, 300), (179, 84), (10, 10)]
    (codeMat 458) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane489GenSource0068 :
    QuotientRankAtLeast (spanCodes [258, 181, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 343), (181, 84), (10, 349)]
    (codeMat 470) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0069 :
    QuotientRankAtLeast (spanCodes [258, 182, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(258, 10), (182, 20), (10, 479)]
    (codeMat 229) (codeMat 117) (codeMat 380) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

end QiushiMatmul
