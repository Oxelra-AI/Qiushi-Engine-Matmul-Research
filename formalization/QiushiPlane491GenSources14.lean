import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane278GenFinal
import QiushiPlane336GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0140 :
    QuotientRankAtLeast (spanCodes [131, 80, 32, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(131, 96), (80, 304), (32, 2), (4, 1)]
    (codeMat 273) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0141 :
    QuotientRankAtLeast (spanCodes [130, 84, 33, 9]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(130, 1), (84, 354), (33, 272), (9, 16)]
    (codeMat 157) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0142 :
    QuotientRankAtLeast (spanCodes [139, 80, 40, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(139, 338), (80, 322), (40, 1), (4, 288)]
    (codeMat 442) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0143 :
    QuotientRankAtLeast (spanCodes [135, 84, 36, 9]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(135, 97), (84, 337), (36, 3), (9, 2)]
    (codeMat 171) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0144 :
    QuotientRankAtLeast (spanCodes [142, 84, 44, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(142, 115), (84, 98), (44, 304), (1, 16)]
    (codeMat 143) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0145 :
    QuotientRankAtLeast (spanCodes [140, 84, 45, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(140, 354), (84, 370), (45, 1), (2, 256)]
    (codeMat 115) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0146 :
    QuotientRankAtLeast (spanCodes [131, 68, 32, 16]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(131, 96), (68, 336), (32, 2), (16, 1)]
    (codeMat 266) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0147 :
    QuotientRankAtLeast (spanCodes [130, 68, 33, 16]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(130, 2), (68, 304), (33, 96), (16, 1)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0148 :
    QuotientRankAtLeast (spanCodes [128, 70, 35, 18]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(128, 1), (70, 96), (35, 306), (18, 2)]
    (codeMat 92) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0149 :
    QuotientRankAtLeast (spanCodes [143, 73, 44, 29]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(143, 99), (73, 2), (44, 304), (29, 96)]
    (codeMat 143) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
