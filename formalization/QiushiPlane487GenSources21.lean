import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiPlane152GenFinal
import QiushiPlane275GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0210 :
    QuotientRankAtLeast (spanCodes [292, 146, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(292, 3), (146, 2), (84, 99), (10, 338)]
    (codeMat 167) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0211 :
    QuotientRankAtLeast (spanCodes [310, 128, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(310, 17), (128, 16), (84, 99), (10, 338)]
    (codeMat 167) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0212 :
    QuotientRankAtLeast (spanCodes [384, 84, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 2, 1] [(384, 3), (84, 85), (54, 2), (10, 162)]
    (codeMat 95) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane275Gen_lb16

theorem plane487GenSource0213 :
    QuotientRankAtLeast (spanCodes [390, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(390, 3), (84, 99), (48, 2), (10, 306)]
    (codeMat 215) (codeMat 501) (codeMat 494) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0214 :
    QuotientRankAtLeast (spanCodes [404, 84, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(404, 338), (84, 114), (34, 322), (10, 323)]
    (codeMat 250) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0215 :
    QuotientRankAtLeast (spanCodes [277, 151, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 96, 16, 10, 1] [(277, 123), (151, 191), (84, 190), (53, 96), (10, 112)]
    (codeMat 93) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane152Gen_lb16

theorem plane487GenSource0216 :
    QuotientRankAtLeast (spanCodes [80, 32, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(80, 132), (32, 1), (8, 2), (4, 8), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0217 :
    QuotientRankAtLeast (spanCodes [81, 33, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(81, 166), (33, 11), (9, 2), (5, 8), (3, 32)]
    (codeMat 267) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0218 :
    QuotientRankAtLeast (spanCodes [80, 32, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(80, 166), (32, 9), (9, 2), (4, 8), (3, 32)]
    (codeMat 331) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0219 :
    QuotientRankAtLeast (spanCodes [81, 32, 8, 5, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(81, 132), (32, 3), (8, 2), (5, 8), (2, 32)]
    (codeMat 330) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
