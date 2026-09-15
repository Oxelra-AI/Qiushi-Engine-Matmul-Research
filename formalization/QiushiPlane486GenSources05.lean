import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiPlane455GenFinal
import QiushiPlane465GenFinal
import QiushiPlane466GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0050 :
    QuotientRankAtLeast (spanCodes [290, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(290, 30), (68, 129), (10, 149)]
    (codeMat 377) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0051 :
    QuotientRankAtLeast (spanCodes [293, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(293, 10), (68, 129), (10, 149)]
    (codeMat 313) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0052 :
    QuotientRankAtLeast (spanCodes [295, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(295, 30), (68, 129), (10, 149)]
    (codeMat 369) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0053 :
    QuotientRankAtLeast (spanCodes [304, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(304, 304), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0054 :
    QuotientRankAtLeast (spanCodes [305, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(305, 305), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane486GenSource0055 :
    QuotientRankAtLeast (spanCodes [306, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(306, 315), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane486GenSource0056 :
    QuotientRankAtLeast (spanCodes [307, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(307, 314), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0057 :
    QuotientRankAtLeast (spanCodes [308, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(308, 373), (68, 78), (10, 68)]
    (codeMat 249) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane486GenSource0058 :
    QuotientRankAtLeast (spanCodes [309, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(309, 372), (68, 78), (10, 68)]
    (codeMat 249) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane486GenSource0059 :
    QuotientRankAtLeast (spanCodes [310, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(310, 383), (68, 78), (10, 68)]
    (codeMat 241) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

end QiushiMatmul
