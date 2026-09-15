import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane468GenFinal
import QiushiPlane469GenFinal
import QiushiPlane473GenFinal
import QiushiPlane474GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0020 :
    QuotientRankAtLeast (spanCodes [275, 85, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(275, 94), (85, 342), (10, 258)]
    (codeMat 107) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane490GenSource0021 :
    QuotientRankAtLeast (spanCodes [275, 87, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 379), (87, 94), (10, 10)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane490GenSource0022 :
    QuotientRankAtLeast (spanCodes [275, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(275, 250), (96, 240), (10, 164)]
    (codeMat 181) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane490GenSource0023 :
    QuotientRankAtLeast (spanCodes [275, 97, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 382), (97, 276), (10, 96)]
    (codeMat 86) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0024 :
    QuotientRankAtLeast (spanCodes [275, 98, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 379), (98, 303), (10, 293)]
    (codeMat 370) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane490GenSource0025 :
    QuotientRankAtLeast (spanCodes [275, 99, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 94), (99, 84), (10, 300)]
    (codeMat 470) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0026 :
    QuotientRankAtLeast (spanCodes [275, 100, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(275, 94), (100, 240), (10, 164)]
    (codeMat 253) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane490GenSource0027 :
    QuotientRankAtLeast (spanCodes [275, 101, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 286), (101, 276), (10, 96)]
    (codeMat 95) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0028 :
    QuotientRankAtLeast (spanCodes [275, 102, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 370), (102, 84), (10, 300)]
    (codeMat 415) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0029 :
    QuotientRankAtLeast (spanCodes [275, 103, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 94), (103, 303), (10, 293)]
    (codeMat 379) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

end QiushiMatmul
