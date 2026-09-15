import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane426GenFinal
import QiushiPlane454GenFinal
import QiushiPlane456GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0000 :
    QuotientRankAtLeast (spanCodes [274, 10, 1]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 10, 1] [(274, 283), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426Gen_lb18

theorem plane490GenSource0001 :
    QuotientRankAtLeast (spanCodes [259, 16, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 10, 1] [(259, 272), (16, 1), (10, 11)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426Gen_lb18

theorem plane490GenSource0002 :
    QuotientRankAtLeast (spanCodes [258, 17, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 10, 1] [(258, 272), (17, 10), (10, 11)]
    (codeMat 267) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426Gen_lb18

theorem plane490GenSource0003 :
    QuotientRankAtLeast (spanCodes [263, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(263, 126), (20, 10), (10, 30)]
    (codeMat 410) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0004 :
    QuotientRankAtLeast (spanCodes [262, 21, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(262, 126), (21, 20), (10, 30)]
    (codeMat 467) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0005 :
    QuotientRankAtLeast (spanCodes [261, 22, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(261, 191), (22, 20), (10, 30)]
    (codeMat 275) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane490GenSource0006 :
    QuotientRankAtLeast (spanCodes [275, 33, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 106), (33, 10), (10, 30)]
    (codeMat 345) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0007 :
    QuotientRankAtLeast (spanCodes [275, 35, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(275, 181), (35, 10), (10, 30)]
    (codeMat 267) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane490GenSource0008 :
    QuotientRankAtLeast (spanCodes [275, 37, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(275, 116), (37, 10), (10, 30)]
    (codeMat 337) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane490GenSource0009 :
    QuotientRankAtLeast (spanCodes [275, 38, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(275, 171), (38, 10), (10, 30)]
    (codeMat 266) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

end QiushiMatmul
