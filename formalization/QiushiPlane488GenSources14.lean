import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane152GenFinal
import QiushiPlane267GenFinal
import QiushiPlane278GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0140 :
    QuotientRankAtLeast (spanCodes [260, 163, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(260, 1), (163, 99), (96, 97), (10, 338)]
    (codeMat 229) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0141 :
    QuotientRankAtLeast (spanCodes [293, 130, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(293, 306), (130, 1), (96, 304), (10, 97)]
    (codeMat 277) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0142 :
    QuotientRankAtLeast (spanCodes [390, 65, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(390, 1), (65, 2), (33, 304), (10, 336)]
    (codeMat 93) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0143 :
    QuotientRankAtLeast (spanCodes [402, 85, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(402, 338), (85, 337), (53, 304), (10, 306)]
    (codeMat 158) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0144 :
    QuotientRankAtLeast (spanCodes [416, 96, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(416, 306), (96, 304), (10, 97), (7, 1)]
    (codeMat 161) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0145 :
    QuotientRankAtLeast (spanCodes [288, 144, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(288, 2), (144, 1), (96, 34), (10, 118)]
    (codeMat 102) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane488GenSource0146 :
    QuotientRankAtLeast (spanCodes [275, 132, 71, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 96, 16, 10, 1] [(275, 174), (132, 197), (71, 196), (39, 112), (10, 96)]
    (codeMat 93) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane152Gen_lb16

theorem plane488GenSource0147 :
    QuotientRankAtLeast (spanCodes [273, 149, 85, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 96, 16, 10, 1] [(273, 123), (149, 191), (85, 190), (53, 96), (10, 112)]
    (codeMat 92) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane152Gen_lb16

theorem plane488GenSource0148 :
    QuotientRankAtLeast (spanCodes [263, 177, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(263, 306), (177, 305), (96, 97), (10, 338)]
    (codeMat 247) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0149 :
    QuotientRankAtLeast (spanCodes [292, 146, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(292, 2), (146, 1), (96, 336), (10, 97)]
    (codeMat 279) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
