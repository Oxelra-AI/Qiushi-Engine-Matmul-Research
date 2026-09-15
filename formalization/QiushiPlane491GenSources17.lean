import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane278GenFinal
import QiushiPlane336GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0170 :
    QuotientRankAtLeast (spanCodes [142, 65, 45, 21]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(142, 99), (65, 16), (45, 1), (21, 289)]
    (codeMat 491) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0171 :
    QuotientRankAtLeast (spanCodes [147, 84, 48, 8]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(147, 306), (84, 339), (48, 3), (8, 2)]
    (codeMat 226) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0172 :
    QuotientRankAtLeast (spanCodes [135, 79, 36, 27]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(135, 338), (79, 306), (36, 3), (27, 1)]
    (codeMat 275) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0173 :
    QuotientRankAtLeast (spanCodes [140, 68, 47, 16]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(140, 99), (68, 371), (47, 257), (16, 256)]
    (codeMat 179) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0174 :
    QuotientRankAtLeast (spanCodes [148, 84, 55, 8]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(148, 371), (84, 355), (55, 257), (8, 256)]
    (codeMat 163) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0175 :
    QuotientRankAtLeast (spanCodes [155, 83, 56, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(155, 304), (83, 336), (56, 1), (7, 3)]
    (codeMat 282) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0176 :
    QuotientRankAtLeast (spanCodes [256, 163, 84, 8]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 98, 16, 1] [(256, 16), (163, 99), (84, 370), (8, 256)]
    (codeMat 167) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane336Gen_lb16

theorem plane491GenSource0177 :
    QuotientRankAtLeast (spanCodes [264, 163, 83, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(264, 338), (163, 98), (83, 306), (7, 3)]
    (codeMat 247) (codeMat 431) (codeMat 477) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0178 :
    QuotientRankAtLeast (spanCodes [264, 163, 79, 27]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(264, 323), (163, 98), (79, 17), (27, 288)]
    (codeMat 318) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0179 :
    QuotientRankAtLeast (spanCodes [271, 163, 72, 28]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(271, 305), (163, 98), (72, 3), (28, 338)]
    (codeMat 254) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
