import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane468GenFinal
import QiushiPlane469GenFinal
import QiushiPlane470GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0030 :
    QuotientRankAtLeast (spanCodes [183, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(183, 250), (84, 94), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane487GenSource0031 :
    QuotientRankAtLeast (spanCodes [257, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(257, 164), (84, 174), (10, 240)]
    (codeMat 87) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane487GenSource0032 :
    QuotientRankAtLeast (spanCodes [258, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(258, 264), (84, 84), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane487GenSource0033 :
    QuotientRankAtLeast (spanCodes [259, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(259, 259), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane487GenSource0034 :
    QuotientRankAtLeast (spanCodes [261, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(261, 164), (84, 94), (10, 240)]
    (codeMat 95) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane487GenSource0035 :
    QuotientRankAtLeast (spanCodes [262, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(262, 259), (84, 94), (10, 10)]
    (codeMat 345) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane487GenSource0036 :
    QuotientRankAtLeast (spanCodes [263, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(263, 264), (84, 342), (10, 258)]
    (codeMat 107) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane487GenSource0037 :
    QuotientRankAtLeast (spanCodes [272, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(272, 10), (84, 174), (10, 240)]
    (codeMat 86) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane487GenSource0038 :
    QuotientRankAtLeast (spanCodes [274, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(274, 343), (84, 84), (10, 10)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane487GenSource0039 :
    QuotientRankAtLeast (spanCodes [275, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(275, 348), (84, 84), (10, 258)]
    (codeMat 106) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

end QiushiMatmul
