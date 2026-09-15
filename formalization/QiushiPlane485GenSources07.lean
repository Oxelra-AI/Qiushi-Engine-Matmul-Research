import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane455GenFinal
import QiushiPlane456GenFinal
import QiushiPlane457GenFinal
import QiushiPlane458GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0070 :
    QuotientRankAtLeast (spanCodes [419, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(419, 171), (20, 20), (10, 30)]
    (codeMat 403) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane485GenSource0071 :
    QuotientRankAtLeast (spanCodes [421, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(421, 171), (20, 20), (10, 30)]
    (codeMat 467) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane485GenSource0072 :
    QuotientRankAtLeast (spanCodes [422, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(422, 129), (20, 10), (10, 30)]
    (codeMat 346) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane485GenSource0073 :
    QuotientRankAtLeast (spanCodes [423, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(423, 159), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane485GenSource0074 :
    QuotientRankAtLeast (spanCodes [449, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(449, 449), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane485GenSource0075 :
    QuotientRankAtLeast (spanCodes [450, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(450, 450), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0076 :
    QuotientRankAtLeast (spanCodes [451, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(451, 450), (20, 30), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0077 :
    QuotientRankAtLeast (spanCodes [452, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(452, 456), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0078 :
    QuotientRankAtLeast (spanCodes [453, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(453, 456), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0079 :
    QuotientRankAtLeast (spanCodes [454, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(454, 449), (20, 20), (10, 10)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

end QiushiMatmul
