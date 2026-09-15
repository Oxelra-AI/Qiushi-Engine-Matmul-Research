import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit446From373
import QiushiPlane295GenFinal
import QiushiPlane434GenFinal
import QiushiPlane447GenFinal
import QiushiPlane463GenFinal
import QiushiPlane465GenFinal
import QiushiPlane469GenFinal
import QiushiPlane473GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0080 :
    QuotientRankAtLeast (spanCodes [275, 244, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 84, 10] [(275, 342), (244, 84), (10, 264)]
    (codeMat 159) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane469Gen_lb18

theorem plane490GenSource0081 :
    QuotientRankAtLeast (spanCodes [275, 245, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [179, 68, 10] [(275, 253), (245, 10), (10, 68)]
    (codeMat 107) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane463Gen_lb18

theorem plane490GenSource0082 :
    QuotientRankAtLeast (spanCodes [275, 246, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 68, 10] [(275, 382), (246, 10), (10, 68)]
    (codeMat 187) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane465Gen_lb18

theorem plane490GenSource0083 :
    QuotientRankAtLeast (spanCodes [275, 247, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [293, 84, 10] [(275, 379), (247, 94), (10, 10)]
    (codeMat 331) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane473Gen_lb18

theorem plane490GenSource0084 :
    QuotientRankAtLeast (spanCodes [273, 8, 2]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(273, 266), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane490GenSource0085 :
    QuotientRankAtLeast (spanCodes [272, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(272, 283), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane490GenSource0086 :
    QuotientRankAtLeast (spanCodes [257, 18, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(257, 283), (18, 1), (10, 17)]
    (codeMat 275) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane490GenSource0087 :
    QuotientRankAtLeast (spanCodes [256, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(256, 1), (19, 400), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane490GenSource0088 :
    QuotientRankAtLeast (spanCodes [260, 23, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [306, 160, 1] [(260, 1), (23, 160), (10, 402)]
    (codeMat 85) (codeMat 205) (codeMat 242) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane447Gen_lb17

theorem plane490GenSource0089 :
    QuotientRankAtLeast (spanCodes [275, 33, 10, 5]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 305), (33, 33), (10, 43), (5, 1)]
    (codeMat 345) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

end QiushiMatmul
