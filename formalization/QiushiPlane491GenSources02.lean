import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane468GenFinal
import QiushiPlane473GenFinal
import QiushiPlane475GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0020 :
    QuotientRankAtLeast (spanCodes [136, 84, 43]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(136, 175), (84, 106), (43, 96)]
    (codeMat 95) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0021 :
    QuotientRankAtLeast (spanCodes [141, 84, 46]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(141, 84), (84, 94), (46, 293)]
    (codeMat 305) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0022 :
    QuotientRankAtLeast (spanCodes [145, 84, 50]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(145, 276), (84, 286), (50, 96)]
    (codeMat 141) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0023 :
    QuotientRankAtLeast (spanCodes [150, 84, 53]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(150, 175), (84, 106), (53, 96)]
    (codeMat 250) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0024 :
    QuotientRankAtLeast (spanCodes [154, 84, 57]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(154, 96), (84, 286), (57, 276)]
    (codeMat 159) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0025 :
    QuotientRankAtLeast (spanCodes [153, 84, 58]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(153, 10), (84, 369), (58, 293)]
    (codeMat 299) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0026 :
    QuotientRankAtLeast (spanCodes [152, 84, 59]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(152, 293), (84, 379), (59, 10)]
    (codeMat 346) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0027 :
    QuotientRankAtLeast (spanCodes [159, 84, 60]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(159, 382), (84, 106), (60, 96)]
    (codeMat 214) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0028 :
    QuotientRankAtLeast (spanCodes [158, 84, 61]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(158, 94), (84, 250), (61, 240)]
    (codeMat 215) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0029 :
    QuotientRankAtLeast (spanCodes [157, 84, 62]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(157, 379), (84, 94), (62, 10)]
    (codeMat 339) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

end QiushiMatmul
