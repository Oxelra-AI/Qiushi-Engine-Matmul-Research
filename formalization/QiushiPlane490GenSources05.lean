import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane463GenFinal
import QiushiPlane465GenFinal
import QiushiPlane469GenFinal
import QiushiPlane471GenFinal
import QiushiPlane473GenFinal
import QiushiPlane474GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0050 :
    QuotientRankAtLeast (spanCodes [275, 166, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 94), (166, 376), (10, 300)]
    (codeMat 351) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0051 :
    QuotientRankAtLeast (spanCodes [275, 167, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(275, 84), (167, 94), (10, 294)]
    (codeMat 313) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane490GenSource0052 :
    QuotientRankAtLeast (spanCodes [275, 176, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [179, 68, 10] [(275, 185), (176, 78), (10, 68)]
    (codeMat 106) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane463Gen_lb18

theorem plane490GenSource0053 :
    QuotientRankAtLeast (spanCodes [275, 177, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(275, 348), (177, 342), (10, 258)]
    (codeMat 179) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane490GenSource0054 :
    QuotientRankAtLeast (spanCodes [275, 178, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(275, 314), (178, 78), (10, 68)]
    (codeMat 242) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane490GenSource0055 :
    QuotientRankAtLeast (spanCodes [275, 179, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 369), (179, 84), (10, 10)]
    (codeMat 330) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane490GenSource0056 :
    QuotientRankAtLeast (spanCodes [275, 180, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 382), (180, 276), (10, 96)]
    (codeMat 159) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0057 :
    QuotientRankAtLeast (spanCodes [275, 181, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(275, 382), (181, 286), (10, 276)]
    (codeMat 159) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane490GenSource0058 :
    QuotientRankAtLeast (spanCodes [275, 182, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 369), (182, 10), (10, 293)]
    (codeMat 355) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane490GenSource0059 :
    QuotientRankAtLeast (spanCodes [275, 183, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(275, 299), (183, 94), (10, 383)]
    (codeMat 125) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

end QiushiMatmul
