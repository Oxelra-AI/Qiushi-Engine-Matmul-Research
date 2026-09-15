import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
import QiushiPlane455GenFinal
import QiushiPlane456GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0030 :
    QuotientRankAtLeast (spanCodes [224, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(224, 191), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane485GenSource0031 :
    QuotientRankAtLeast (spanCodes [225, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(225, 159), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane485GenSource0032 :
    QuotientRankAtLeast (spanCodes [226, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(226, 159), (20, 30), (10, 20)]
    (codeMat 459) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane485GenSource0033 :
    QuotientRankAtLeast (spanCodes [227, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(227, 191), (20, 30), (10, 20)]
    (codeMat 459) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane485GenSource0034 :
    QuotientRankAtLeast (spanCodes [228, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(228, 149), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane485GenSource0035 :
    QuotientRankAtLeast (spanCodes [229, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(229, 181), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane485GenSource0036 :
    QuotientRankAtLeast (spanCodes [230, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(230, 181), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane485GenSource0037 :
    QuotientRankAtLeast (spanCodes [231, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(231, 149), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane485GenSource0038 :
    QuotientRankAtLeast (spanCodes [257, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(257, 96), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 80), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

end QiushiMatmul
