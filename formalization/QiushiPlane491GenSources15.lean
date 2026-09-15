import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0150 :
    QuotientRankAtLeast (spanCodes [128, 68, 35, 16]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(128, 1), (68, 97), (35, 272), (16, 2)]
    (codeMat 84) (codeMat 99) (codeMat 172) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0151 :
    QuotientRankAtLeast (spanCodes [139, 79, 40, 27]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(139, 17), (79, 323), (40, 288), (27, 16)]
    (codeMat 94) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0152 :
    QuotientRankAtLeast (spanCodes [140, 72, 47, 28]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(140, 337), (72, 3), (47, 96), (28, 336)]
    (codeMat 94) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0153 :
    QuotientRankAtLeast (spanCodes [144, 84, 49, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(144, 1), (84, 339), (49, 306), (2, 2)]
    (codeMat 206) (codeMat 359) (codeMat 174) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0154 :
    QuotientRankAtLeast (spanCodes [130, 65, 33, 21]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(130, 2), (65, 1), (33, 96), (21, 336)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0155 :
    QuotientRankAtLeast (spanCodes [143, 76, 44, 24]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(143, 99), (76, 96), (44, 304), (24, 2)]
    (codeMat 87) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0156 :
    QuotientRankAtLeast (spanCodes [140, 79, 47, 27]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(140, 305), (79, 306), (47, 96), (27, 1)]
    (codeMat 115) (codeMat 317) (codeMat 285) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0157 :
    QuotientRankAtLeast (spanCodes [128, 65, 35, 21]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(128, 16), (65, 288), (35, 323), (21, 322)]
    (codeMat 99) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0158 :
    QuotientRankAtLeast (spanCodes [135, 70, 36, 18]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(135, 336), (70, 96), (36, 3), (18, 2)]
    (codeMat 99) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0159 :
    QuotientRankAtLeast (spanCodes [142, 79, 45, 27]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(142, 98), (79, 368), (45, 1), (27, 2)]
    (codeMat 115) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

end QiushiMatmul
