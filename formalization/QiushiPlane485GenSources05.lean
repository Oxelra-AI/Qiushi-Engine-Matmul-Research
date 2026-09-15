import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0050 :
    QuotientRankAtLeast (spanCodes [321, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(321, 96), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0051 :
    QuotientRankAtLeast (spanCodes [322, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(322, 126), (20, 20), (10, 30)]
    (codeMat 403) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0052 :
    QuotientRankAtLeast (spanCodes [323, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(323, 80), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane485GenSource0053 :
    QuotientRankAtLeast (spanCodes [324, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(324, 96), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0054 :
    QuotientRankAtLeast (spanCodes [326, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(326, 80), (20, 30), (10, 20)]
    (codeMat 331) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane485GenSource0055 :
    QuotientRankAtLeast (spanCodes [327, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(327, 126), (20, 20), (10, 30)]
    (codeMat 467) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0056 :
    QuotientRankAtLeast (spanCodes [352, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(352, 96), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0057 :
    QuotientRankAtLeast (spanCodes [353, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(353, 68), (20, 20), (10, 30)]
    (codeMat 339) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane485GenSource0058 :
    QuotientRankAtLeast (spanCodes [355, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(355, 116), (20, 30), (10, 20)]
    (codeMat 395) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0059 :
    QuotientRankAtLeast (spanCodes [356, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(356, 68), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

end QiushiMatmul
