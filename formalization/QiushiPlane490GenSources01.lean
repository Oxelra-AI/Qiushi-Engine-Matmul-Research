import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane456GenFinal
import QiushiPlane463GenFinal
import QiushiPlane464GenFinal
import QiushiPlane465GenFinal
import QiushiPlane469GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0010 :
    QuotientRankAtLeast (spanCodes [275, 49, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 116), (49, 20), (10, 30)]
    (codeMat 459) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0011 :
    QuotientRankAtLeast (spanCodes [275, 52, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 106), (52, 10), (10, 30)]
    (codeMat 394) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0012 :
    QuotientRankAtLeast (spanCodes [275, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(275, 250), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane490GenSource0013 :
    QuotientRankAtLeast (spanCodes [275, 69, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [179, 68, 10] [(275, 253), (69, 78), (10, 68)]
    (codeMat 177) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane463Gen_lb18

theorem plane490GenSource0014 :
    QuotientRankAtLeast (spanCodes [275, 70, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(275, 314), (70, 10), (10, 68)]
    (codeMat 169) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane490GenSource0015 :
    QuotientRankAtLeast (spanCodes [275, 71, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(275, 382), (71, 10), (10, 68)]
    (codeMat 233) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane490GenSource0016 :
    QuotientRankAtLeast (spanCodes [275, 80, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 106), (80, 10), (10, 30)]
    (codeMat 372) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0017 :
    QuotientRankAtLeast (spanCodes [275, 81, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 116), (81, 20), (10, 30)]
    (codeMat 380) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0018 :
    QuotientRankAtLeast (spanCodes [275, 82, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(275, 181), (82, 10), (10, 30)]
    (codeMat 423) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane490GenSource0019 :
    QuotientRankAtLeast (spanCodes [275, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(275, 348), (84, 84), (10, 258)]
    (codeMat 106) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

end QiushiMatmul
