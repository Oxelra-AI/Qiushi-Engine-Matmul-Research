import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane457GenFinal
import QiushiPlane458GenFinal
import QiushiPlane464GenFinal
import QiushiPlane471GenFinal
import QiushiStep132Orbit451AuditedAlias
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0030 :
    QuotientRankAtLeast (spanCodes [258, 97, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 96), (97, 20), (10, 126)]
    (codeMat 377) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0031 :
    QuotientRankAtLeast (spanCodes [258, 98, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [257, 19, 10] [(258, 257), (98, 267), (10, 280)]
    (codeMat 84) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step132_orbit451_span257_19_10_lb18

theorem plane489GenSource0032 :
    QuotientRankAtLeast (spanCodes [258, 99, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 450), (99, 470), (10, 476)]
    (codeMat 239) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0033 :
    QuotientRankAtLeast (spanCodes [258, 100, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 126), (100, 20), (10, 96)]
    (codeMat 249) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0034 :
    QuotientRankAtLeast (spanCodes [258, 102, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 456), (102, 470), (10, 476)]
    (codeMat 181) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0035 :
    QuotientRankAtLeast (spanCodes [258, 103, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(258, 469), (103, 459), (10, 479)]
    (codeMat 230) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane489GenSource0036 :
    QuotientRankAtLeast (spanCodes [258, 112, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 96), (112, 20), (10, 126)]
    (codeMat 358) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 113, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(258, 68), (113, 78), (10, 240)]
    (codeMat 93) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane489GenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 114, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 456), (114, 470), (10, 450)]
    (codeMat 98) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 115, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(258, 10), (115, 94), (10, 383)]
    (codeMat 229) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

end QiushiMatmul
