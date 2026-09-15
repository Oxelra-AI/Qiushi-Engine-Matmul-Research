import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane336GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0200 :
    QuotientRankAtLeast (spanCodes [292, 162, 84, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(292, 1), (162, 17), (84, 339), (1, 288)]
    (codeMat 303) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0201 :
    QuotientRankAtLeast (spanCodes [264, 155, 84, 56]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(264, 368), (155, 97), (84, 275), (56, 3)]
    (codeMat 239) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0202 :
    QuotientRankAtLeast (spanCodes [275, 128, 84, 35]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 115), (128, 1), (84, 98), (35, 338)]
    (codeMat 236) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0203 :
    QuotientRankAtLeast (spanCodes [288, 163, 68, 16]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(288, 16), (163, 339), (68, 322), (16, 288)]
    (codeMat 309) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0204 :
    QuotientRankAtLeast (spanCodes [292, 163, 64, 20]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(292, 16), (163, 305), (64, 1), (20, 338)]
    (codeMat 188) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0205 :
    QuotientRankAtLeast (spanCodes [293, 163, 65, 21]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(293, 371), (163, 370), (65, 3), (21, 274)]
    (codeMat 229) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0206 :
    QuotientRankAtLeast (spanCodes [260, 144, 84, 51]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(260, 16), (144, 1), (84, 273), (51, 371)]
    (codeMat 302) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0207 :
    QuotientRankAtLeast (spanCodes [276, 128, 84, 35]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(276, 97), (128, 1), (84, 98), (35, 338)]
    (codeMat 236) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0208 :
    QuotientRankAtLeast (spanCodes [293, 163, 70, 18]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(293, 371), (163, 370), (70, 17), (18, 256)]
    (codeMat 229) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0209 :
    QuotientRankAtLeast (spanCodes [304, 163, 83, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(304, 336), (163, 307), (83, 97), (7, 3)]
    (codeMat 229) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
