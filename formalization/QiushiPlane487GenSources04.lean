import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane468GenFinal
import QiushiPlane469GenFinal
import QiushiPlane470GenFinal
import QiushiPlane471GenFinal
import QiushiPlane472GenFinal
import QiushiPlane473GenFinal
import QiushiPlane474GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0040 :
    QuotientRankAtLeast (spanCodes [277, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(277, 250), (84, 94), (10, 240)]
    (codeMat 94) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane487GenSource0041 :
    QuotientRankAtLeast (spanCodes [278, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(278, 349), (84, 94), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane487GenSource0042 :
    QuotientRankAtLeast (spanCodes [279, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(279, 94), (84, 342), (10, 258)]
    (codeMat 99) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane487GenSource0043 :
    QuotientRankAtLeast (spanCodes [289, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(289, 289), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane487GenSource0044 :
    QuotientRankAtLeast (spanCodes [290, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 84, 10] [(290, 10), (84, 380), (10, 296)]
    (codeMat 206) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane472Gen_lb18

theorem plane487GenSource0045 :
    QuotientRankAtLeast (spanCodes [291, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 84, 10] [(291, 10), (84, 84), (10, 296)]
    (codeMat 142) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane472Gen_lb18

theorem plane487GenSource0046 :
    QuotientRankAtLeast (spanCodes [293, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(293, 293), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane487GenSource0047 :
    QuotientRankAtLeast (spanCodes [294, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(294, 294), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane487GenSource0048 :
    QuotientRankAtLeast (spanCodes [295, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(295, 294), (84, 94), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane487GenSource0049 :
    QuotientRankAtLeast (spanCodes [304, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 84, 10] [(304, 374), (84, 84), (10, 296)]
    (codeMat 143) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane472Gen_lb18

end QiushiMatmul
