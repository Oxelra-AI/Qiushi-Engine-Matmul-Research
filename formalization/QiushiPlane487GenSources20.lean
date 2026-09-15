import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane278GenFinal
import QiushiPlane338GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0200 :
    QuotientRankAtLeast (spanCodes [292, 148, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(292, 288), (148, 289), (84, 305), (10, 338)]
    (codeMat 230) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0201 :
    QuotientRankAtLeast (spanCodes [310, 134, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(310, 96), (134, 97), (84, 305), (10, 338)]
    (codeMat 230) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0202 :
    QuotientRankAtLeast (spanCodes [390, 84, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(390, 3), (84, 337), (54, 2), (10, 306)]
    (codeMat 158) (codeMat 115) (codeMat 492) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane487GenSource0203 :
    QuotientRankAtLeast (spanCodes [404, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 98, 16, 1] [(404, 17), (84, 305), (36, 1), (10, 323)]
    (codeMat 179) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane338Gen_lb16

theorem plane487GenSource0204 :
    QuotientRankAtLeast (spanCodes [386, 66, 38, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(386, 264), (66, 280), (38, 69), (22, 68), (10, 259)]
    (codeMat 98) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0205 :
    QuotientRankAtLeast (spanCodes [390, 66, 35, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(390, 16), (66, 280), (35, 69), (22, 327), (10, 259)]
    (codeMat 107) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0206 :
    QuotientRankAtLeast (spanCodes [390, 67, 37, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(390, 16), (67, 280), (37, 326), (23, 68), (10, 259)]
    (codeMat 106) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0207 :
    QuotientRankAtLeast (spanCodes [290, 144, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(290, 11), (144, 1), (82, 332), (10, 264), (6, 16)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0208 :
    QuotientRankAtLeast (spanCodes [387, 67, 33, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(387, 264), (67, 280), (33, 326), (23, 327), (10, 259)]
    (codeMat 99) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane487GenSource0209 :
    QuotientRankAtLeast (spanCodes [304, 131, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(304, 343), (131, 333), (82, 68), (10, 264), (6, 16)]
    (codeMat 207) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

end QiushiMatmul
