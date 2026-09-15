import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane278GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0120 :
    QuotientRankAtLeast (spanCodes [390, 65, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(390, 2), (65, 1), (20, 304), (10, 96)]
    (codeMat 141) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0121 :
    QuotientRankAtLeast (spanCodes [262, 198, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(262, 264), (198, 280), (32, 1), (20, 69), (10, 326)]
    (codeMat 98) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane485GenSource0122 :
    QuotientRankAtLeast (spanCodes [292, 197, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(292, 1), (197, 338), (20, 96), (10, 304)]
    (codeMat 87) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0123 :
    QuotientRankAtLeast (spanCodes [359, 134, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(359, 305), (134, 338), (20, 336), (10, 304)]
    (codeMat 95) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0124 :
    QuotientRankAtLeast (spanCodes [418, 67, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(418, 306), (67, 97), (20, 304), (10, 96)]
    (codeMat 143) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0125 :
    QuotientRankAtLeast (spanCodes [258, 195, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 264), (195, 16), (32, 1), (20, 69), (10, 327)]
    (codeMat 106) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane485GenSource0126 :
    QuotientRankAtLeast (spanCodes [288, 198, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(288, 1), (198, 338), (20, 96), (10, 304)]
    (codeMat 86) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0127 :
    QuotientRankAtLeast (spanCodes [354, 132, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(354, 305), (132, 338), (20, 336), (10, 304)]
    (codeMat 94) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0128 :
    QuotientRankAtLeast (spanCodes [420, 66, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(420, 306), (66, 97), (20, 304), (10, 96)]
    (codeMat 142) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane485GenSource0129 :
    QuotientRankAtLeast (spanCodes [323, 130, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(323, 264), (130, 16), (39, 326), (20, 258), (10, 327)]
    (codeMat 107) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

end QiushiMatmul
