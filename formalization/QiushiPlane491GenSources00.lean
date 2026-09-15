import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane467GenFinal
import QiushiPlane468GenFinal
import QiushiPlane473GenFinal
import QiushiPlane475GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0000 :
    QuotientRankAtLeast (spanCodes [163, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(163, 247), (84, 163), (10, 10)]
    (codeMat 267) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

theorem plane491GenSource0001 :
    QuotientRankAtLeast (spanCodes [163, 84, 11]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(163, 250), (84, 84), (11, 10)]
    (codeMat 401) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0002 :
    QuotientRankAtLeast (spanCodes [163, 84, 12]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(163, 106), (84, 165), (12, 96)]
    (codeMat 107) (codeMat 354) (codeMat 142) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0003 :
    QuotientRankAtLeast (spanCodes [163, 84, 13]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(163, 94), (84, 303), (13, 293)]
    (codeMat 314) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0004 :
    QuotientRankAtLeast (spanCodes [163, 84, 14]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(163, 106), (84, 372), (14, 96)]
    (codeMat 95) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0005 :
    QuotientRankAtLeast (spanCodes [163, 84, 15]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(163, 250), (84, 84), (15, 164)]
    (codeMat 230) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0006 :
    QuotientRankAtLeast (spanCodes [163, 69, 17]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(163, 174), (69, 240), (17, 10)]
    (codeMat 331) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0007 :
    QuotientRankAtLeast (spanCodes [163, 71, 19]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(163, 207), (71, 96), (19, 10)]
    (codeMat 345) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0008 :
    QuotientRankAtLeast (spanCodes [163, 66, 22]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(163, 94), (66, 293), (22, 10)]
    (codeMat 409) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0009 :
    QuotientRankAtLeast (spanCodes [163, 67, 23]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(163, 106), (67, 96), (23, 197)]
    (codeMat 98) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

end QiushiMatmul
