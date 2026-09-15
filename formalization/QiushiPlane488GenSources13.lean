import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane152GenFinal
import QiushiPlane267GenFinal
import QiushiPlane275GenFinal
import QiushiPlane276GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0130 :
    QuotientRankAtLeast (spanCodes [288, 96, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(288, 32), (96, 34), (10, 118), (5, 1)]
    (codeMat 417) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane488GenSource0131 :
    QuotientRankAtLeast (spanCodes [260, 130, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(260, 1), (130, 2), (96, 96), (10, 274)]
    (codeMat 165) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane488GenSource0132 :
    QuotientRankAtLeast (spanCodes [293, 163, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 2, 1] [(293, 160), (163, 161), (96, 162), (10, 246)]
    (codeMat 117) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane275Gen_lb16

theorem plane488GenSource0133 :
    QuotientRankAtLeast (spanCodes [384, 96, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(384, 1), (96, 96), (10, 274), (6, 2)]
    (codeMat 140) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane488GenSource0134 :
    QuotientRankAtLeast (spanCodes [263, 146, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(263, 97), (146, 2), (96, 368), (10, 274)]
    (codeMat 167) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane488GenSource0135 :
    QuotientRankAtLeast (spanCodes [402, 96, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(402, 371), (96, 96), (10, 274), (7, 2)]
    (codeMat 142) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane488GenSource0136 :
    QuotientRankAtLeast (spanCodes [291, 178, 96, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(291, 17), (178, 79), (96, 332), (10, 280), (7, 16)]
    (codeMat 207) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane488GenSource0137 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(288, 32), (128, 1), (96, 34), (10, 118)]
    (codeMat 116) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane488GenSource0138 :
    QuotientRankAtLeast (spanCodes [275, 132, 86, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 96, 16, 10, 1] [(275, 213), (132, 191), (86, 206), (54, 16), (10, 112)]
    (codeMat 94) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane152Gen_lb16

theorem plane488GenSource0139 :
    QuotientRankAtLeast (spanCodes [263, 147, 80, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(263, 78), (147, 332), (80, 333), (48, 16), (10, 264)]
    (codeMat 213) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

end QiushiMatmul
