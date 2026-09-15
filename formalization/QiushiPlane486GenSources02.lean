import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiPlane455GenFinal
import QiushiPlane459GenFinal
import QiushiPlane461GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0020 :
    QuotientRankAtLeast (spanCodes [151, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(151, 30), (68, 149), (10, 129)]
    (codeMat 241) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0021 :
    QuotientRankAtLeast (spanCodes [160, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 10] [(160, 10), (68, 68), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane459Gen_lb18

theorem plane486GenSource0022 :
    QuotientRankAtLeast (spanCodes [162, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(162, 162), (68, 68), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0023 :
    QuotientRankAtLeast (spanCodes [163, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(163, 230), (68, 68), (10, 10)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0024 :
    QuotientRankAtLeast (spanCodes [164, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(164, 162), (68, 10), (10, 68)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0025 :
    QuotientRankAtLeast (spanCodes [165, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(165, 230), (68, 10), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0026 :
    QuotientRankAtLeast (spanCodes [166, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(166, 162), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0027 :
    QuotientRankAtLeast (spanCodes [167, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(167, 230), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0028 :
    QuotientRankAtLeast (spanCodes [176, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(176, 68), (68, 168), (10, 10)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane486GenSource0029 :
    QuotientRankAtLeast (spanCodes [177, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(177, 230), (68, 168), (10, 10)]
    (codeMat 267) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

end QiushiMatmul
