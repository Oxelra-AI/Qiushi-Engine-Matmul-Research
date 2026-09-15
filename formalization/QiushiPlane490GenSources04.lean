import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane464GenFinal
import QiushiPlane465GenFinal
import QiushiPlane468GenFinal
import QiushiPlane469GenFinal
import QiushiPlane471GenFinal
import QiushiPlane473GenFinal
import QiushiPlane474GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0040 :
    QuotientRankAtLeast (spanCodes [275, 134, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 94), (134, 10), (10, 293)]
    (codeMat 425) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane490GenSource0041 :
    QuotientRankAtLeast (spanCodes [275, 135, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 370), (135, 376), (10, 294)]
    (codeMat 299) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0042 :
    QuotientRankAtLeast (spanCodes [275, 145, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 106), (145, 20), (10, 30)]
    (codeMat 444) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0043 :
    QuotientRankAtLeast (spanCodes [275, 148, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 286), (148, 276), (10, 96)]
    (codeMat 141) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0044 :
    QuotientRankAtLeast (spanCodes [275, 150, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 370), (150, 376), (10, 300)]
    (codeMat 461) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0045 :
    QuotientRankAtLeast (spanCodes [275, 151, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(275, 84), (151, 289), (10, 383)]
    (codeMat 239) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane490GenSource0046 :
    QuotientRankAtLeast (spanCodes [275, 160, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(275, 190), (160, 78), (10, 68)]
    (codeMat 122) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane490GenSource0047 :
    QuotientRankAtLeast (spanCodes [275, 161, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(275, 342), (161, 84), (10, 264)]
    (codeMat 86) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane490GenSource0048 :
    QuotientRankAtLeast (spanCodes [275, 162, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(275, 382), (162, 78), (10, 68)]
    (codeMat 114) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane490GenSource0049 :
    QuotientRankAtLeast (spanCodes [275, 164, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(275, 250), (164, 240), (10, 164)]
    (codeMat 254) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

end QiushiMatmul
