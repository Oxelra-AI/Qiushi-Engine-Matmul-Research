import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane456GenFinal
import QiushiPlane461GenFinal
import QiushiPlane464GenFinal
import QiushiPlane468GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0010 :
    QuotientRankAtLeast (spanCodes [87, 55, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(87, 171), (55, 20), (10, 10)]
    (codeMat 267) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane488GenSource0011 :
    QuotientRankAtLeast (spanCodes [129, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(129, 20), (96, 96), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0012 :
    QuotientRankAtLeast (spanCodes [131, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(131, 30), (96, 126), (10, 10)]
    (codeMat 474) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0013 :
    QuotientRankAtLeast (spanCodes [132, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(132, 168), (96, 162), (10, 68)]
    (codeMat 99) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane488GenSource0014 :
    QuotientRankAtLeast (spanCodes [133, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(133, 240), (96, 164), (10, 10)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane488GenSource0015 :
    QuotientRankAtLeast (spanCodes [134, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(134, 164), (96, 240), (10, 10)]
    (codeMat 275) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane488GenSource0016 :
    QuotientRankAtLeast (spanCodes [135, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(135, 240), (96, 180), (10, 10)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane488GenSource0017 :
    QuotientRankAtLeast (spanCodes [145, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(145, 20), (96, 96), (10, 10)]
    (codeMat 394) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0018 :
    QuotientRankAtLeast (spanCodes [147, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(147, 30), (96, 126), (10, 10)]
    (codeMat 346) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0019 :
    QuotientRankAtLeast (spanCodes [148, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(148, 240), (96, 164), (10, 10)]
    (codeMat 395) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

end QiushiMatmul
