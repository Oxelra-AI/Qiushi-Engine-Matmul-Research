import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane452GenFinal
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0000 :
    QuotientRankAtLeast (spanCodes [35, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [35, 20, 10] [(35, 35), (20, 10), (10, 61)]
    (codeMat 267) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane452Gen_lb18

theorem plane485GenSource0001 :
    QuotientRankAtLeast (spanCodes [37, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [35, 20, 10] [(37, 41), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane452Gen_lb18

theorem plane485GenSource0002 :
    QuotientRankAtLeast (spanCodes [68, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(68, 68), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane485GenSource0003 :
    QuotientRankAtLeast (spanCodes [69, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(69, 68), (20, 30), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane485GenSource0004 :
    QuotientRankAtLeast (spanCodes [70, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(70, 78), (20, 20), (10, 10)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane485GenSource0005 :
    QuotientRankAtLeast (spanCodes [71, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(71, 78), (20, 30), (10, 10)]
    (codeMat 409) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane485GenSource0006 :
    QuotientRankAtLeast (spanCodes [96, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(96, 96), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0007 :
    QuotientRankAtLeast (spanCodes [97, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(97, 96), (20, 20), (10, 10)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0008 :
    QuotientRankAtLeast (spanCodes [98, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(98, 106), (20, 20), (10, 10)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane485GenSource0009 :
    QuotientRankAtLeast (spanCodes [99, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(99, 106), (20, 20), (10, 10)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

end QiushiMatmul
