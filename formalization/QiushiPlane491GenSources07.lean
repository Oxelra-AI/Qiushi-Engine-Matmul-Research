import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane315GenFinal
import QiushiPlane467GenFinal
import QiushiPlane468GenFinal
import QiushiPlane473GenFinal
import QiushiPlane475GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0070 :
    QuotientRankAtLeast (spanCodes [309, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(309, 382), (163, 372), (84, 286)]
    (codeMat 239) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0071 :
    QuotientRankAtLeast (spanCodes [310, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(310, 10), (163, 379), (84, 84)]
    (codeMat 156) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0072 :
    QuotientRankAtLeast (spanCodes [312, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(312, 10), (163, 207), (84, 106)]
    (codeMat 86) (codeMat 250) (codeMat 397) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane491GenSource0073 :
    QuotientRankAtLeast (spanCodes [314, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(314, 247), (163, 94), (84, 253)]
    (codeMat 142) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

theorem plane491GenSource0074 :
    QuotientRankAtLeast (spanCodes [315, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(315, 10), (163, 286), (84, 106)]
    (codeMat 117) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane491GenSource0075 :
    QuotientRankAtLeast (spanCodes [317, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(317, 379), (163, 369), (84, 94)]
    (codeMat 239) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane491GenSource0076 :
    QuotientRankAtLeast (spanCodes [318, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(318, 94), (163, 174), (84, 250)]
    (codeMat 412) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0077 :
    QuotientRankAtLeast (spanCodes [319, 163, 84]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 84, 10] [(319, 240), (163, 174), (84, 250)]
    (codeMat 313) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane468Gen_lb18

theorem plane491GenSource0078 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(160, 10), (68, 170), (16, 1), (3, 260)]
    (codeMat 226) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0079 :
    QuotientRankAtLeast (spanCodes [162, 70, 18, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(162, 420), (70, 10), (18, 260), (1, 1)]
    (codeMat 161) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
