import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane468GenFinal
import QiushiPlane475GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0010 :
    QuotientRankAtLeast (spanCodes [163, 77, 25]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(163, 106), (77, 175), (25, 10)]
    (codeMat 339) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0011 :
    QuotientRankAtLeast (spanCodes [163, 78, 26]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(163, 84), (78, 164), (26, 10)]
    (codeMat 474) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0012 :
    QuotientRankAtLeast (spanCodes [163, 74, 30]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(163, 250), (74, 164), (30, 240)]
    (codeMat 93) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0013 :
    QuotientRankAtLeast (spanCodes [163, 75, 31]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(163, 106), (75, 96), (31, 276)]
    (codeMat 86) (codeMat 500) (codeMat 94) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0014 :
    QuotientRankAtLeast (spanCodes [129, 84, 34]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(129, 240), (84, 174), (34, 164)]
    (codeMat 103) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0015 :
    QuotientRankAtLeast (spanCodes [134, 84, 37]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(134, 10), (84, 165), (37, 96)]
    (codeMat 141) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0016 :
    QuotientRankAtLeast (spanCodes [133, 84, 38]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(133, 276), (84, 286), (38, 96)]
    (codeMat 107) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0017 :
    QuotientRankAtLeast (spanCodes [132, 84, 39]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(132, 10), (84, 250), (39, 164)]
    (codeMat 165) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0018 :
    QuotientRankAtLeast (spanCodes [138, 84, 41]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(138, 164), (84, 174), (41, 240)]
    (codeMat 142) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0019 :
    QuotientRankAtLeast (spanCodes [137, 84, 42]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(137, 197), (84, 207), (42, 96)]
    (codeMat 177) (codeMat 485) (codeMat 171) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

end QiushiMatmul
