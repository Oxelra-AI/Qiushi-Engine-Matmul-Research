import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiPlane455GenFinal
import QiushiPlane465GenFinal
import QiushiPlane466GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0060 :
    QuotientRankAtLeast (spanCodes [311, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(311, 382), (68, 78), (10, 68)]
    (codeMat 241) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0061 :
    QuotientRankAtLeast (spanCodes [385, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(385, 10), (68, 20), (10, 149)]
    (codeMat 417) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0062 :
    QuotientRankAtLeast (spanCodes [386, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(386, 30), (68, 20), (10, 149)]
    (codeMat 489) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0063 :
    QuotientRankAtLeast (spanCodes [389, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(389, 30), (68, 20), (10, 149)]
    (codeMat 481) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0064 :
    QuotientRankAtLeast (spanCodes [391, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(391, 10), (68, 20), (10, 149)]
    (codeMat 425) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0065 :
    QuotientRankAtLeast (spanCodes [400, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(400, 304), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0066 :
    QuotientRankAtLeast (spanCodes [401, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(401, 305), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane486GenSource0067 :
    QuotientRankAtLeast (spanCodes [402, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(402, 315), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane486GenSource0068 :
    QuotientRankAtLeast (spanCodes [403, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(403, 314), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0069 :
    QuotientRankAtLeast (spanCodes [404, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(404, 383), (68, 10), (10, 68)]
    (codeMat 225) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

end QiushiMatmul
