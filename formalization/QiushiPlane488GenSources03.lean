import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane426GenFinal
import QiushiPlane454GenFinal
import QiushiPlane456GenFinal
import QiushiPlane465GenFinal
import QiushiPlane472GenFinal
import QiushiPlane475GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0030 :
    QuotientRankAtLeast (spanCodes [179, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(179, 181), (96, 191), (10, 20)]
    (codeMat 213) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane488GenSource0031 :
    QuotientRankAtLeast (spanCodes [180, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(180, 197), (96, 96), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane488GenSource0032 :
    QuotientRankAtLeast (spanCodes [181, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 84, 10] [(181, 380), (96, 290), (10, 374)]
    (codeMat 124) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane472Gen_lb18

theorem plane488GenSource0033 :
    QuotientRankAtLeast (spanCodes [182, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(182, 96), (96, 197), (10, 10)]
    (codeMat 282) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane488GenSource0034 :
    QuotientRankAtLeast (spanCodes [183, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(183, 314), (96, 78), (10, 304)]
    (codeMat 94) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane488GenSource0035 :
    QuotientRankAtLeast (spanCodes [256, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 10, 1] [(256, 1), (96, 10), (10, 272)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426Gen_lb18

theorem plane488GenSource0036 :
    QuotientRankAtLeast (spanCodes [257, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(257, 10), (96, 20), (10, 96)]
    (codeMat 161) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 10, 1] [(258, 283), (96, 10), (10, 272)]
    (codeMat 86) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426Gen_lb18

theorem plane488GenSource0038 :
    QuotientRankAtLeast (spanCodes [259, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(259, 126), (96, 20), (10, 96)]
    (codeMat 177) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0039 :
    QuotientRankAtLeast (spanCodes [261, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(261, 10), (96, 20), (10, 126)]
    (codeMat 417) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

end QiushiMatmul
