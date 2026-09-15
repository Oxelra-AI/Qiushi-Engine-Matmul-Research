import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit118From31
import QiushiPlane270GenFinal
import QiushiPlane278GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0120 :
    QuotientRankAtLeast (spanCodes [258, 209, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(258, 338), (209, 97), (38, 336), (10, 96)]
    (codeMat 95) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane489GenSource0121 :
    QuotientRankAtLeast (spanCodes [258, 240, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(258, 338), (240, 97), (10, 306), (7, 2)]
    (codeMat 142) (codeMat 346) (codeMat 459) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane489GenSource0122 :
    QuotientRankAtLeast (spanCodes [256, 8, 5, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(256, 32), (8, 320), (5, 1), (2, 2)]
    (codeMat 161) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0123 :
    QuotientRankAtLeast (spanCodes [258, 34, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(258, 34), (34, 33), (10, 353), (6, 32)]
    (codeMat 107) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0124 :
    QuotientRankAtLeast (spanCodes [256, 36, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(256, 2), (36, 1), (8, 320), (2, 32)]
    (codeMat 99) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0125 :
    QuotientRankAtLeast (spanCodes [258, 34, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(258, 353), (34, 321), (18, 320), (10, 323)]
    (codeMat 242) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0126 :
    QuotientRankAtLeast (spanCodes [256, 48, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [320, 32, 2, 1] [(256, 32), (48, 1), (8, 2), (2, 320)]
    (codeMat 98) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane270Gen_lb15

theorem plane489GenSource0127 :
    QuotientRankAtLeast (spanCodes [257, 36, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(257, 136), (36, 2), (20, 47), (9, 3), (3, 32)]
    (codeMat 331) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane489GenSource0128 :
    QuotientRankAtLeast (spanCodes [258, 32, 18, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 164), (32, 2), (18, 32), (10, 35), (7, 9)]
    (codeMat 282) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0129 :
    QuotientRankAtLeast (spanCodes [257, 49, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 133), (49, 33), (9, 40), (4, 2), (3, 3)]
    (codeMat 281) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
