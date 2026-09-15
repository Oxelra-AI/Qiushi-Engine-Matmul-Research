import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiPlane278GenFinal
import QiushiPlane336GenFinal
import QiushiWcOrbit147Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0210 :
    QuotientRankAtLeast (spanCodes [264, 146, 84, 49]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(264, 306), (146, 3), (84, 337), (49, 97)]
    (codeMat 351) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0211 :
    QuotientRankAtLeast (spanCodes [271, 149, 84, 54]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(271, 99), (149, 17), (84, 354), (54, 256)]
    (codeMat 247) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0212 :
    QuotientRankAtLeast (spanCodes [276, 142, 84, 45]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(276, 306), (142, 99), (84, 305), (45, 1)]
    (codeMat 379) (codeMat 342) (codeMat 215) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0213 :
    QuotientRankAtLeast (spanCodes [304, 163, 84, 9]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(304, 371), (163, 273), (84, 114), (9, 256)]
    (codeMat 239) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0214 :
    QuotientRankAtLeast (spanCodes [260, 155, 84, 56]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(260, 16), (155, 371), (84, 273), (56, 256)]
    (codeMat 174) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0215 :
    QuotientRankAtLeast (spanCodes [276, 139, 84, 40]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(276, 97), (139, 306), (84, 98), (40, 1)]
    (codeMat 370) (codeMat 171) (codeMat 485) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0216 :
    QuotientRankAtLeast (spanCodes [288, 163, 72, 28]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(288, 1), (163, 339), (72, 3), (28, 97)]
    (codeMat 342) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0217 :
    QuotientRankAtLeast (spanCodes [292, 163, 76, 24]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(292, 16), (163, 355), (76, 17), (24, 256)]
    (codeMat 190) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0218 :
    QuotientRankAtLeast (spanCodes [275, 138, 81, 41, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 16, 10, 1] [(275, 94), (138, 255), (81, 228), (41, 160), (5, 16)]
    (codeMat 142) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit147_lb16_wc

theorem plane491GenSource0219 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
