import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane425GenFinal
import QiushiPlane426GenFinal
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
import QiushiPlane455GenFinal
import QiushiPlane466GenFinal
import QiushiPlane470GenFinal
import QiushiPlane474GenFinal
import QiushiStep132Orbit451AuditedAlias
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0040 :
    QuotientRankAtLeast (spanCodes [258, 116, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 265), (116, 94), (10, 259)]
    (codeMat 114) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0041 :
    QuotientRankAtLeast (spanCodes [258, 117, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 10), (117, 84), (10, 349)]
    (codeMat 461) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 118, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(258, 300), (118, 376), (10, 294)]
    (codeMat 482) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane489GenSource0043 :
    QuotientRankAtLeast (spanCodes [258, 119, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(258, 68), (119, 78), (10, 383)]
    (codeMat 125) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane489GenSource0044 :
    QuotientRankAtLeast (spanCodes [258, 128, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 10, 1] [(258, 10), (128, 1), (10, 264)]
    (codeMat 140) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane425Gen_lb18

theorem plane489GenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 129, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 20), (129, 10), (10, 80)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0046 :
    QuotientRankAtLeast (spanCodes [258, 131, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(258, 30), (131, 10), (10, 139)]
    (codeMat 492) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane489GenSource0047 :
    QuotientRankAtLeast (spanCodes [258, 132, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 10, 1] [(258, 11), (132, 10), (10, 272)]
    (codeMat 141) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426Gen_lb18

theorem plane489GenSource0048 :
    QuotientRankAtLeast (spanCodes [258, 133, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 30), (133, 20), (10, 126)]
    (codeMat 421) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0049 :
    QuotientRankAtLeast (spanCodes [258, 134, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(258, 25), (134, 19), (10, 280)]
    (codeMat 140) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

end QiushiMatmul
