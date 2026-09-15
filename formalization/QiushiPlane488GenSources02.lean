import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane455GenFinal
import QiushiPlane456GenFinal
import QiushiPlane461GenFinal
import QiushiPlane464GenFinal
import QiushiPlane465GenFinal
import QiushiPlane468GenFinal
import QiushiPlane472GenFinal
import QiushiPlane475GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0020 :
    QuotientRankAtLeast (spanCodes [149, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(149, 168), (96, 162), (10, 68)]
    (codeMat 115) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane488GenSource0021 :
    QuotientRankAtLeast (spanCodes [150, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(150, 180), (96, 240), (10, 10)]
    (codeMat 275) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane488GenSource0022 :
    QuotientRankAtLeast (spanCodes [151, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(151, 164), (96, 240), (10, 10)]
    (codeMat 403) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane488GenSource0023 :
    QuotientRankAtLeast (spanCodes [161, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(161, 161), (96, 191), (10, 20)]
    (codeMat 215) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane488GenSource0024 :
    QuotientRankAtLeast (spanCodes [162, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(162, 149), (96, 30), (10, 129)]
    (codeMat 242) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane488GenSource0025 :
    QuotientRankAtLeast (spanCodes [164, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(164, 10), (96, 78), (10, 304)]
    (codeMat 92) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane488GenSource0026 :
    QuotientRankAtLeast (spanCodes [165, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(165, 165), (96, 96), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane488GenSource0027 :
    QuotientRankAtLeast (spanCodes [166, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 84, 10] [(166, 10), (96, 290), (10, 374)]
    (codeMat 110) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane472Gen_lb18

theorem plane488GenSource0028 :
    QuotientRankAtLeast (spanCodes [167, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(167, 165), (96, 197), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane488GenSource0029 :
    QuotientRankAtLeast (spanCodes [176, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(176, 20), (96, 30), (10, 129)]
    (codeMat 226) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

end QiushiMatmul
