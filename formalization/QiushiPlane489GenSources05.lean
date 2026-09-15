import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
import QiushiPlane455GenFinal
import QiushiPlane458GenFinal
import QiushiPlane464GenFinal
import QiushiPlane469GenFinal
import QiushiPlane471GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0050 :
    QuotientRankAtLeast (spanCodes [258, 135, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 10), (135, 20), (10, 450)]
    (codeMat 161) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0051 :
    QuotientRankAtLeast (spanCodes [258, 145, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 126), (145, 20), (10, 30)]
    (codeMat 444) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0052 :
    QuotientRankAtLeast (spanCodes [258, 147, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 456), (147, 30), (10, 20)]
    (codeMat 157) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0053 :
    QuotientRankAtLeast (spanCodes [258, 148, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 30), (148, 20), (10, 126)]
    (codeMat 442) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0054 :
    QuotientRankAtLeast (spanCodes [258, 149, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(258, 180), (149, 78), (10, 240)]
    (codeMat 158) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane489GenSource0055 :
    QuotientRankAtLeast (spanCodes [258, 150, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 30), (150, 10), (10, 476)]
    (codeMat 247) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0056 :
    QuotientRankAtLeast (spanCodes [258, 151, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(258, 373), (151, 289), (10, 383)]
    (codeMat 230) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane489GenSource0057 :
    QuotientRankAtLeast (spanCodes [258, 160, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 80), (160, 10), (10, 68)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0058 :
    QuotientRankAtLeast (spanCodes [258, 161, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(258, 258), (161, 84), (10, 264)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane489GenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 162, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(258, 139), (162, 129), (10, 149)]
    (codeMat 498) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

end QiushiMatmul
