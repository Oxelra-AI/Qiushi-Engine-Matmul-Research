import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0190 :
    QuotientRankAtLeast (spanCodes [256, 135, 84, 36]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(256, 2), (135, 338), (84, 307), (36, 3)]
    (codeMat 167) (codeMat 158) (codeMat 358) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0191 :
    QuotientRankAtLeast (spanCodes [264, 143, 84, 44]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(264, 272), (143, 369), (84, 370), (44, 274)]
    (codeMat 167) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0192 :
    QuotientRankAtLeast (spanCodes [275, 148, 84, 55]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 114), (148, 304), (84, 305), (55, 338)]
    (codeMat 116) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0193 :
    QuotientRankAtLeast (spanCodes [277, 146, 84, 49]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(277, 339), (146, 3), (84, 307), (49, 338)]
    (codeMat 111) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0194 :
    QuotientRankAtLeast (spanCodes [288, 163, 80, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(288, 2), (163, 370), (80, 274), (4, 3)]
    (codeMat 183) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0195 :
    QuotientRankAtLeast (spanCodes [264, 142, 84, 45]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(264, 338), (142, 114), (84, 305), (45, 16)]
    (codeMat 415) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0196 :
    QuotientRankAtLeast (spanCodes [273, 151, 84, 52]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(273, 305), (151, 304), (84, 307), (52, 97)]
    (codeMat 397) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0197 :
    QuotientRankAtLeast (spanCodes [275, 149, 84, 54]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(275, 98), (149, 96), (84, 370), (54, 3)]
    (codeMat 110) (codeMat 461) (codeMat 234) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0198 :
    QuotientRankAtLeast (spanCodes [277, 147, 84, 48]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(277, 307), (147, 306), (84, 339), (48, 3)]
    (codeMat 125) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0199 :
    QuotientRankAtLeast (spanCodes [288, 163, 81, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(288, 288), (163, 305), (81, 323), (5, 16)]
    (codeMat 461) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

end QiushiMatmul
