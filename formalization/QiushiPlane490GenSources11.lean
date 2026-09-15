import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane295GenFinal
import QiushiPlane315GenFinal
import QiushiStep107Orbit373Extraction
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0110 :
    QuotientRankAtLeast (spanCodes [275, 145, 64, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 305), (145, 10), (64, 32), (10, 43)]
    (codeMat 311) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0111 :
    QuotientRankAtLeast (spanCodes [275, 149, 71, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 431), (149, 430), (71, 10), (10, 160)]
    (codeMat 205) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0112 :
    QuotientRankAtLeast (spanCodes [275, 146, 70, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 271), (146, 260), (70, 10), (10, 160)]
    (codeMat 141) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0113 :
    QuotientRankAtLeast (spanCodes [275, 162, 67, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 431), (162, 170), (67, 420), (10, 160)]
    (codeMat 86) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0114 :
    QuotientRankAtLeast (spanCodes [275, 165, 66, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 271), (165, 270), (66, 420), (10, 160)]
    (codeMat 95) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0115 :
    QuotientRankAtLeast (spanCodes [275, 225, 10, 6]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 421), (225, 270), (10, 170), (6, 260)]
    (codeMat 478) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0116 :
    QuotientRankAtLeast (spanCodes [275, 130, 116, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 431), (130, 260), (116, 270), (10, 160)]
    (codeMat 159) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0117 :
    QuotientRankAtLeast (spanCodes [275, 212, 34, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 271), (212, 270), (34, 430), (10, 170)]
    (codeMat 477) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0118 :
    QuotientRankAtLeast (spanCodes [256, 229, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(256, 1), (229, 460), (19, 472), (10, 312)]
    (codeMat 92) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane490GenSource0119 :
    QuotientRankAtLeast (spanCodes [273, 8, 4, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(273, 84), (8, 32), (4, 1), (2, 2)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

end QiushiMatmul
