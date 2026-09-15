import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane456GenFinal
import QiushiPlane468GenFinal
import QiushiPlane471GenFinal
import QiushiPlane474GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0030 :
    QuotientRankAtLeast (spanCodes [275, 112, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 382), (112, 10), (10, 276)]
    (codeMat 86) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0031 :
    QuotientRankAtLeast (spanCodes [275, 114, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 84), (114, 94), (10, 294)]
    (codeMat 307) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0032 :
    QuotientRankAtLeast (spanCodes [275, 115, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(275, 299), (115, 94), (10, 383)]
    (codeMat 247) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane490GenSource0033 :
    QuotientRankAtLeast (spanCodes [275, 117, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 106), (117, 286), (10, 276)]
    (codeMat 95) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0034 :
    QuotientRankAtLeast (spanCodes [275, 118, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 370), (118, 376), (10, 294)]
    (codeMat 314) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0035 :
    QuotientRankAtLeast (spanCodes [275, 119, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(275, 84), (119, 289), (10, 383)]
    (codeMat 190) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane490GenSource0036 :
    QuotientRankAtLeast (spanCodes [275, 129, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 116), (129, 10), (10, 30)]
    (codeMat 428) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0037 :
    QuotientRankAtLeast (spanCodes [275, 131, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(275, 171), (131, 20), (10, 30)]
    (codeMat 359) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane490GenSource0038 :
    QuotientRankAtLeast (spanCodes [275, 132, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(275, 94), (132, 240), (10, 164)]
    (codeMat 110) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane490GenSource0039 :
    QuotientRankAtLeast (spanCodes [275, 133, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 286), (133, 276), (10, 96)]
    (codeMat 106) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

end QiushiMatmul
