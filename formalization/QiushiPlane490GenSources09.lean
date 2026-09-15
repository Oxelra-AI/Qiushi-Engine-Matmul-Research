import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane295GenFinal
import QiushiPlane315GenFinal
import QiushiPlane447GenFinal
import QiushiStep107Orbit373Extraction
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0090 :
    QuotientRankAtLeast (spanCodes [275, 32, 10, 5]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 282), (32, 32), (10, 43), (5, 1)]
    (codeMat 337) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0091 :
    QuotientRankAtLeast (spanCodes [263, 36, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(263, 283), (36, 32), (20, 33), (10, 43)]
    (codeMat 346) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0092 :
    QuotientRankAtLeast (spanCodes [275, 51, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [306, 160, 1] [(275, 307), (51, 306), (10, 160)]
    (codeMat 86) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane447Gen_lb17

theorem plane490GenSource0093 :
    QuotientRankAtLeast (spanCodes [275, 48, 10, 4]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 305), (48, 1), (10, 43), (4, 32)]
    (codeMat 394) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0094 :
    QuotientRankAtLeast (spanCodes [262, 32, 21, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(262, 283), (32, 32), (21, 10), (10, 43)]
    (codeMat 339) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0095 :
    QuotientRankAtLeast (spanCodes [275, 49, 10, 4]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 314), (49, 10), (10, 43), (4, 32)]
    (codeMat 395) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0096 :
    QuotientRankAtLeast (spanCodes [275, 55, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [306, 160, 1] [(275, 403), (55, 402), (10, 306)]
    (codeMat 87) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane447Gen_lb17

theorem plane490GenSource0097 :
    QuotientRankAtLeast (spanCodes [275, 83, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [306, 160, 1] [(275, 307), (83, 306), (10, 160)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane447Gen_lb17

theorem plane490GenSource0098 :
    QuotientRankAtLeast (spanCodes [256, 71, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(256, 1), (71, 20), (19, 472), (10, 312)]
    (codeMat 140) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane490GenSource0099 :
    QuotientRankAtLeast (spanCodes [275, 71, 54, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 271), (71, 160), (54, 260), (10, 170)]
    (codeMat 334) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
