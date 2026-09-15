import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane336GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0130 :
    QuotientRankAtLeast (spanCodes [163, 64, 18, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(163, 370), (64, 1), (18, 16), (6, 256)]
    (codeMat 92) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0131 :
    QuotientRankAtLeast (spanCodes [163, 65, 16, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(163, 98), (65, 1), (16, 16), (5, 288)]
    (codeMat 213) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0132 :
    QuotientRankAtLeast (spanCodes [162, 64, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(162, 96), (64, 3), (20, 272), (1, 2)]
    (codeMat 141) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0133 :
    QuotientRankAtLeast (spanCodes [163, 64, 20, 8]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(163, 337), (64, 1), (20, 306), (8, 2)]
    (codeMat 212) (codeMat 419) (codeMat 183) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0134 :
    QuotientRankAtLeast (spanCodes [163, 65, 21, 9]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(163, 98), (65, 1), (21, 304), (9, 2)]
    (codeMat 157) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0135 :
    QuotientRankAtLeast (spanCodes [163, 73, 24, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(163, 115), (73, 1), (24, 16), (5, 256)]
    (codeMat 87) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0136 :
    QuotientRankAtLeast (spanCodes [163, 73, 27, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(163, 355), (73, 1), (27, 16), (6, 256)]
    (codeMat 95) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0137 :
    QuotientRankAtLeast (spanCodes [162, 72, 28, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(162, 306), (72, 3), (28, 97), (1, 1)]
    (codeMat 185) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0138 :
    QuotientRankAtLeast (spanCodes [130, 84, 32, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(130, 16), (84, 354), (32, 1), (1, 256)]
    (codeMat 106) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0139 :
    QuotientRankAtLeast (spanCodes [128, 84, 32, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(128, 16), (84, 114), (32, 1), (3, 256)]
    (codeMat 98) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

end QiushiMatmul
