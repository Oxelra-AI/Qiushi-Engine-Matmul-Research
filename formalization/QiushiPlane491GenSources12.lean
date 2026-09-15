import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane315GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0120 :
    QuotientRankAtLeast (spanCodes [288, 163, 76, 24]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(288, 1), (163, 421), (76, 10), (24, 260)]
    (codeMat 318) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0121 :
    QuotientRankAtLeast (spanCodes [275, 137, 84, 42]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 271), (137, 430), (84, 171), (42, 160)]
    (codeMat 94) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0122 :
    QuotientRankAtLeast (spanCodes [300, 163, 65, 21]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(300, 261), (163, 270), (65, 1), (21, 160)]
    (codeMat 157) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0123 :
    QuotientRankAtLeast (spanCodes [272, 143, 84, 44]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(272, 170), (143, 271), (84, 270), (44, 160)]
    (codeMat 87) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0124 :
    QuotientRankAtLeast (spanCodes [304, 163, 84, 12]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(304, 170), (163, 421), (84, 270), (12, 160)]
    (codeMat 213) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0125 :
    QuotientRankAtLeast (spanCodes [162, 80, 4, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(162, 96), (80, 274), (4, 1), (1, 2)]
    (codeMat 169) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0126 :
    QuotientRankAtLeast (spanCodes [160, 80, 4, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(160, 96), (80, 304), (4, 1), (3, 2)]
    (codeMat 161) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0127 :
    QuotientRankAtLeast (spanCodes [161, 81, 5, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(161, 339), (81, 306), (5, 1), (2, 2)]
    (codeMat 241) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0128 :
    QuotientRankAtLeast (spanCodes [162, 82, 6, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(162, 306), (82, 96), (6, 2), (1, 1)]
    (codeMat 281) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0129 :
    QuotientRankAtLeast (spanCodes [163, 64, 16, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(163, 98), (64, 288), (16, 1), (4, 16)]
    (codeMat 330) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

end QiushiMatmul
