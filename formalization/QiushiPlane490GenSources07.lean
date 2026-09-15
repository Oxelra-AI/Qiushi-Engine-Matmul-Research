import QiushiPlane490GenData
import QiushiCertifiedTransport
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

theorem plane490GenSource0070 :
    QuotientRankAtLeast (spanCodes [275, 224, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(275, 94), (224, 240), (10, 164)]
    (codeMat 183) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane490GenSource0071 :
    QuotientRankAtLeast (spanCodes [275, 226, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 370), (226, 94), (10, 294)]
    (codeMat 305) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0072 :
    QuotientRankAtLeast (spanCodes [275, 227, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 370), (227, 376), (10, 300)]
    (codeMat 342) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0073 :
    QuotientRankAtLeast (spanCodes [275, 228, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(275, 250), (228, 78), (10, 68)]
    (codeMat 115) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane490GenSource0074 :
    QuotientRankAtLeast (spanCodes [275, 229, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(275, 94), (229, 84), (10, 264)]
    (codeMat 95) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane490GenSource0075 :
    QuotientRankAtLeast (spanCodes [275, 231, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(275, 314), (231, 78), (10, 68)]
    (codeMat 123) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane490GenSource0076 :
    QuotientRankAtLeast (spanCodes [275, 240, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 286), (240, 276), (10, 96)]
    (codeMat 179) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0077 :
    QuotientRankAtLeast (spanCodes [275, 241, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 286), (241, 372), (10, 96)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0078 :
    QuotientRankAtLeast (spanCodes [275, 242, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 84), (242, 303), (10, 293)]
    (codeMat 354) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane490GenSource0079 :
    QuotientRankAtLeast (spanCodes [275, 243, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(275, 84), (243, 289), (10, 383)]
    (codeMat 117) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

end QiushiMatmul
