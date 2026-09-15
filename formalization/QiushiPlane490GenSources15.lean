import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane275GenFinal
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0150 :
    QuotientRankAtLeast (spanCodes [275, 146, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 305), (146, 16), (10, 322), (7, 1)]
    (codeMat 185) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane490GenSource0151 :
    QuotientRankAtLeast (spanCodes [275, 147, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 339), (147, 336), (10, 304), (6, 2)]
    (codeMat 205) (codeMat 460) (codeMat 122) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0152 :
    QuotientRankAtLeast (spanCodes [275, 144, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 339), (144, 1), (51, 336), (10, 96)]
    (codeMat 86) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0153 :
    QuotientRankAtLeast (spanCodes [275, 147, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 307), (147, 304), (48, 1), (10, 96)]
    (codeMat 114) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0154 :
    QuotientRankAtLeast (spanCodes [275, 130, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(275, 115), (130, 16), (39, 323), (10, 322)]
    (codeMat 171) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane490GenSource0155 :
    QuotientRankAtLeast (spanCodes [275, 146, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 99), (146, 2), (55, 96), (10, 336)]
    (codeMat 143) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0156 :
    QuotientRankAtLeast (spanCodes [275, 147, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(275, 99), (147, 96), (54, 2), (10, 304)]
    (codeMat 95) (codeMat 396) (codeMat 106) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane490GenSource0157 :
    QuotientRankAtLeast (spanCodes [275, 149, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(275, 99), (149, 96), (48, 2), (10, 274)]
    (codeMat 87) (codeMat 397) (codeMat 250) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane490GenSource0158 :
    QuotientRankAtLeast (spanCodes [275, 163, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 2, 1] [(275, 86), (163, 85), (10, 162), (6, 2)]
    (codeMat 143) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane275Gen_lb16

theorem plane490GenSource0159 :
    QuotientRankAtLeast (spanCodes [275, 144, 49, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(275, 94), (144, 16), (49, 68), (10, 258), (6, 1)]
    (codeMat 177) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

end QiushiMatmul
