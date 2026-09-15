import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiPlane461GenFinal
import QiushiPlane462GenFinal
import QiushiPlane463GenFinal
import QiushiPlane464GenFinal
import QiushiPlane465GenFinal
import QiushiPlane466GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0070 :
    QuotientRankAtLeast (spanCodes [405, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(405, 382), (68, 10), (10, 68)]
    (codeMat 225) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0071 :
    QuotientRankAtLeast (spanCodes [406, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(406, 373), (68, 10), (10, 68)]
    (codeMat 233) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane486GenSource0072 :
    QuotientRankAtLeast (spanCodes [407, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(407, 372), (68, 10), (10, 68)]
    (codeMat 233) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0073 :
    QuotientRankAtLeast (spanCodes [416, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(416, 68), (68, 10), (10, 168)]
    (codeMat 140) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0074 :
    QuotientRankAtLeast (spanCodes [417, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(417, 230), (68, 10), (10, 168)]
    (codeMat 141) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0075 :
    QuotientRankAtLeast (spanCodes [418, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(418, 180), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane486GenSource0076 :
    QuotientRankAtLeast (spanCodes [419, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(419, 250), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane486GenSource0077 :
    QuotientRankAtLeast (spanCodes [420, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [178, 68, 10] [(420, 78), (68, 10), (10, 184)]
    (codeMat 140) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane462Gen_lb18

theorem plane486GenSource0078 :
    QuotientRankAtLeast (spanCodes [421, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [179, 68, 10] [(421, 179), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane463Gen_lb18

theorem plane486GenSource0079 :
    QuotientRankAtLeast (spanCodes [422, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(422, 180), (68, 10), (10, 78)]
    (codeMat 417) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

end QiushiMatmul
