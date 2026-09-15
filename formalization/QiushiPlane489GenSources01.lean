import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane425GenFinal
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
import QiushiPlane455GenFinal
import QiushiPlane457GenFinal
import QiushiPlane458GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0010 :
    QuotientRankAtLeast (spanCodes [258, 33, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 68), (33, 10), (10, 20)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0011 :
    QuotientRankAtLeast (spanCodes [258, 35, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(258, 149), (35, 20), (10, 30)]
    (codeMat 473) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane489GenSource0012 :
    QuotientRankAtLeast (spanCodes [258, 37, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 78), (37, 10), (10, 30)]
    (codeMat 401) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 49, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 96), (49, 20), (10, 30)]
    (codeMat 331) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 51, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 456), (51, 30), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0015 :
    QuotientRankAtLeast (spanCodes [258, 52, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 80), (52, 10), (10, 30)]
    (codeMat 330) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0016 :
    QuotientRankAtLeast (spanCodes [258, 55, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(258, 449), (55, 10), (10, 30)]
    (codeMat 337) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane489GenSource0017 :
    QuotientRankAtLeast (spanCodes [258, 64, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 10, 1] [(258, 258), (64, 1), (10, 264)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane425Gen_lb18

theorem plane489GenSource0018 :
    QuotientRankAtLeast (spanCodes [258, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 20), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0019 :
    QuotientRankAtLeast (spanCodes [258, 69, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 30), (69, 10), (10, 78)]
    (codeMat 417) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

end QiushiMatmul
