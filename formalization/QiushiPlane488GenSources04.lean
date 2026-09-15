import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane456GenFinal
import QiushiPlane468GenFinal
import QiushiPlane470GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0040 :
    QuotientRankAtLeast (spanCodes [262, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(262, 96), (96, 20), (10, 126)]
    (codeMat 305) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0041 :
    QuotientRankAtLeast (spanCodes [272, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(272, 10), (96, 20), (10, 96)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0042 :
    QuotientRankAtLeast (spanCodes [273, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(273, 174), (96, 240), (10, 164)]
    (codeMat 167) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane488GenSource0043 :
    QuotientRankAtLeast (spanCodes [274, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(274, 126), (96, 20), (10, 96)]
    (codeMat 86) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0044 :
    QuotientRankAtLeast (spanCodes [275, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(275, 250), (96, 240), (10, 164)]
    (codeMat 181) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane488GenSource0045 :
    QuotientRankAtLeast (spanCodes [276, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(276, 10), (96, 276), (10, 96)]
    (codeMat 85) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane488GenSource0046 :
    QuotientRankAtLeast (spanCodes [277, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(277, 94), (96, 259), (10, 343)]
    (codeMat 444) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane488GenSource0047 :
    QuotientRankAtLeast (spanCodes [278, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(278, 10), (96, 259), (10, 343)]
    (codeMat 302) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane488GenSource0048 :
    QuotientRankAtLeast (spanCodes [279, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(279, 382), (96, 276), (10, 96)]
    (codeMat 87) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane488GenSource0049 :
    QuotientRankAtLeast (spanCodes [289, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(289, 10), (96, 30), (10, 191)]
    (codeMat 335) (codeMat 187) (codeMat 229) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

end QiushiMatmul
