import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane425GenFinal
import QiushiPlane426GenFinal
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
import QiushiPlane455GenFinal
import QiushiPlane458GenFinal
import QiushiStep132Orbit451AuditedAlias
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0000 :
    QuotientRankAtLeast (spanCodes [258, 10, 1]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 10, 1] [(258, 258), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane425Gen_lb18

theorem plane489GenSource0001 :
    QuotientRankAtLeast (spanCodes [258, 10, 4]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 10, 1] [(258, 10), (10, 258), (4, 1)]
    (codeMat 161) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane425Gen_lb18

theorem plane489GenSource0002 :
    QuotientRankAtLeast (spanCodes [258, 16, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 10, 1] [(258, 264), (16, 1), (10, 10)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane425Gen_lb18

theorem plane489GenSource0003 :
    QuotientRankAtLeast (spanCodes [258, 17, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 10, 1] [(258, 272), (17, 10), (10, 11)]
    (codeMat 267) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426Gen_lb18

theorem plane489GenSource0004 :
    QuotientRankAtLeast (spanCodes [258, 19, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(258, 280), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

theorem plane489GenSource0005 :
    QuotientRankAtLeast (spanCodes [258, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 80), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0006 :
    QuotientRankAtLeast (spanCodes [258, 21, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 126), (21, 20), (10, 30)]
    (codeMat 403) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0007 :
    QuotientRankAtLeast (spanCodes [258, 22, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(258, 139), (22, 10), (10, 30)]
    (codeMat 474) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane489GenSource0008 :
    QuotientRankAtLeast (spanCodes [258, 23, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 450), (23, 20), (10, 10)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0009 :
    QuotientRankAtLeast (spanCodes [258, 32, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 10, 1] [(258, 264), (32, 1), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane425Gen_lb18

end QiushiMatmul
