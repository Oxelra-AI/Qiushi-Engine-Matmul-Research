import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0180 :
    QuotientRankAtLeast (spanCodes [275, 195, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 305), (195, 16), (34, 323), (10, 322)]
    (codeMat 234) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane490GenSource0181 :
    QuotientRankAtLeast (spanCodes [275, 210, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 339), (210, 306), (51, 336), (10, 304)]
    (codeMat 142) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0182 :
    QuotientRankAtLeast (spanCodes [275, 211, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 339), (211, 336), (50, 306), (10, 304)]
    (codeMat 86) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0183 :
    QuotientRankAtLeast (spanCodes [275, 212, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(275, 369), (212, 370), (53, 272), (10, 274)]
    (codeMat 94) (codeMat 415) (codeMat 253) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane490GenSource0184 :
    QuotientRankAtLeast (spanCodes [275, 129, 83, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(275, 94), (129, 332), (83, 69), (48, 16), (10, 264)]
    (codeMat 214) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0185 :
    QuotientRankAtLeast (spanCodes [275, 145, 66, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(275, 342), (145, 68), (66, 265), (48, 16), (10, 264)]
    (codeMat 86) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0186 :
    QuotientRankAtLeast (spanCodes [275, 147, 67, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(275, 94), (147, 69), (67, 265), (53, 280), (10, 264)]
    (codeMat 95) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0187 :
    QuotientRankAtLeast (spanCodes [275, 209, 51, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(275, 275), (209, 349), (51, 259), (10, 326), (7, 1)]
    (codeMat 177) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0188 :
    QuotientRankAtLeast (spanCodes [275, 209, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 307), (209, 97), (55, 304), (10, 96)]
    (codeMat 95) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0189 :
    QuotientRankAtLeast (spanCodes [275, 211, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 339), (211, 336), (53, 97), (10, 96)]
    (codeMat 123) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
