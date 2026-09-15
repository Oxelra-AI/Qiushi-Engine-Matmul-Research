import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane456GenFinal
import QiushiPlane457GenFinal
import QiushiPlane458GenFinal
import QiushiPlane471GenFinal
import QiushiPlane473GenFinal
import QiushiPlane475GenFinal
import QiushiStep132Orbit451AuditedAlias
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0050 :
    QuotientRankAtLeast (spanCodes [290, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(290, 274), (96, 19), (10, 280)]
    (codeMat 84) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

theorem plane488GenSource0051 :
    QuotientRankAtLeast (spanCodes [291, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(291, 449), (96, 20), (10, 479)]
    (codeMat 167) (codeMat 158) (codeMat 358) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane488GenSource0052 :
    QuotientRankAtLeast (spanCodes [294, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(294, 450), (96, 10), (10, 476)]
    (codeMat 244) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane488GenSource0053 :
    QuotientRankAtLeast (spanCodes [295, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(295, 456), (96, 10), (10, 476)]
    (codeMat 230) (codeMat 171) (codeMat 485) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane488GenSource0054 :
    QuotientRankAtLeast (spanCodes [304, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(304, 20), (96, 30), (10, 191)]
    (codeMat 230) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane488GenSource0055 :
    QuotientRankAtLeast (spanCodes [305, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(305, 94), (96, 10), (10, 289)]
    (codeMat 354) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane488GenSource0056 :
    QuotientRankAtLeast (spanCodes [306, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(306, 469), (96, 10), (10, 449)]
    (codeMat 98) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane488GenSource0057 :
    QuotientRankAtLeast (spanCodes [307, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(307, 369), (96, 10), (10, 293)]
    (codeMat 370) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane488GenSource0058 :
    QuotientRankAtLeast (spanCodes [308, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(308, 175), (96, 197), (10, 96)]
    (codeMat 107) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane488GenSource0059 :
    QuotientRankAtLeast (spanCodes [309, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(309, 106), (96, 197), (10, 96)]
    (codeMat 123) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

end QiushiMatmul
