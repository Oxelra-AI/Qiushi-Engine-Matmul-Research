import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane458GenFinal
import QiushiPlane464GenFinal
import QiushiPlane466GenFinal
import QiushiPlane470GenFinal
import QiushiPlane471GenFinal
import QiushiPlane474GenFinal
import QiushiPlane475GenFinal
import QiushiPlane476GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0070 :
    QuotientRankAtLeast (spanCodes [403, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 96, 10] [(403, 382), (96, 10), (10, 276)]
    (codeMat 86) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane476Gen_lb18

theorem plane488GenSource0071 :
    QuotientRankAtLeast (spanCodes [404, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(404, 259), (96, 343), (10, 265)]
    (codeMat 253) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane488GenSource0072 :
    QuotientRankAtLeast (spanCodes [406, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(406, 343), (96, 349), (10, 259)]
    (codeMat 99) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane488GenSource0073 :
    QuotientRankAtLeast (spanCodes [407, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(407, 250), (96, 78), (10, 240)]
    (codeMat 94) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane488GenSource0074 :
    QuotientRankAtLeast (spanCodes [417, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [165, 96, 10] [(417, 207), (96, 175), (10, 197)]
    (codeMat 107) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane475Gen_lb18

theorem plane488GenSource0075 :
    QuotientRankAtLeast (spanCodes [418, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(418, 476), (96, 20), (10, 450)]
    (codeMat 98) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane488GenSource0076 :
    QuotientRankAtLeast (spanCodes [419, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(419, 84), (96, 376), (10, 294)]
    (codeMat 419) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane488GenSource0077 :
    QuotientRankAtLeast (spanCodes [420, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(420, 10), (96, 78), (10, 383)]
    (codeMat 124) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane488GenSource0078 :
    QuotientRankAtLeast (spanCodes [421, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(421, 299), (96, 289), (10, 383)]
    (codeMat 236) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane488GenSource0079 :
    QuotientRankAtLeast (spanCodes [422, 96, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(422, 300), (96, 10), (10, 376)]
    (codeMat 212) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

end QiushiMatmul
