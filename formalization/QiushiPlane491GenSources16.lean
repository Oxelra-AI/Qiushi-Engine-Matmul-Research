import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0160 :
    QuotientRankAtLeast (spanCodes [147, 82, 48, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(147, 336), (82, 96), (48, 3), (6, 2)]
    (codeMat 267) (codeMat 396) (codeMat 106) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0161 :
    QuotientRankAtLeast (spanCodes [144, 81, 51, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(144, 16), (81, 338), (51, 289), (5, 1)]
    (codeMat 369) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0162 :
    QuotientRankAtLeast (spanCodes [128, 64, 35, 20]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(128, 2), (64, 3), (35, 96), (20, 272)]
    (codeMat 84) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0163 :
    QuotientRankAtLeast (spanCodes [143, 79, 44, 27]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(143, 99), (79, 96), (44, 274), (27, 2)]
    (codeMat 95) (codeMat 486) (codeMat 157) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0164 :
    QuotientRankAtLeast (spanCodes [144, 80, 51, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(144, 288), (80, 304), (51, 322), (4, 1)]
    (codeMat 161) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0165 :
    QuotientRankAtLeast (spanCodes [148, 84, 52, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(148, 336), (84, 337), (52, 304), (3, 2)]
    (codeMat 140) (codeMat 225) (codeMat 169) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane491GenSource0166 :
    QuotientRankAtLeast (spanCodes [148, 84, 54, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(148, 322), (84, 98), (54, 16), (1, 1)]
    (codeMat 473) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0167 :
    QuotientRankAtLeast (spanCodes [128, 79, 35, 27]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(128, 288), (79, 338), (35, 17), (27, 1)]
    (codeMat 403) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane491GenSource0168 :
    QuotientRankAtLeast (spanCodes [139, 68, 40, 16]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(139, 272), (68, 97), (40, 1), (16, 2)]
    (codeMat 234) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane491GenSource0169 :
    QuotientRankAtLeast (spanCodes [143, 64, 44, 20]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(143, 115), (64, 16), (44, 322), (20, 323)]
    (codeMat 226) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

end QiushiMatmul
