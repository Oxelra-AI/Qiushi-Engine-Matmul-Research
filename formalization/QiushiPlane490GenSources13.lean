import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane274GenFinal
import QiushiPlane278GenFinal
import QiushiPlane298GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0130 :
    QuotientRankAtLeast (spanCodes [275, 48, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 2, 1] [(275, 242), (48, 1), (10, 83), (6, 3)]
    (codeMat 346) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274Gen_lb16

theorem plane490GenSource0131 :
    QuotientRankAtLeast (spanCodes [275, 51, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 417), (51, 33), (10, 42), (5, 32)]
    (codeMat 395) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0132 :
    QuotientRankAtLeast (spanCodes [275, 48, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 417), (48, 32), (10, 42), (7, 1)]
    (codeMat 465) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0133 :
    QuotientRankAtLeast (spanCodes [275, 50, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 395), (50, 43), (10, 42), (5, 32)]
    (codeMat 458) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0134 :
    QuotientRankAtLeast (spanCodes [273, 64, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(273, 84), (64, 1), (8, 2), (2, 32)]
    (codeMat 84) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0135 :
    QuotientRankAtLeast (spanCodes [272, 64, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(272, 118), (64, 1), (9, 2), (3, 32)]
    (codeMat 92) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0136 :
    QuotientRankAtLeast (spanCodes [260, 65, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(260, 3), (65, 1), (23, 304), (10, 96)]
    (codeMat 141) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0137 :
    QuotientRankAtLeast (spanCodes [275, 83, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 339), (83, 336), (10, 96), (5, 1)]
    (codeMat 169) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0138 :
    QuotientRankAtLeast (spanCodes [275, 66, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 99), (66, 338), (51, 96), (10, 336)]
    (codeMat 94) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0139 :
    QuotientRankAtLeast (spanCodes [275, 67, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 115), (67, 338), (50, 323), (10, 322)]
    (codeMat 122) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

end QiushiMatmul
