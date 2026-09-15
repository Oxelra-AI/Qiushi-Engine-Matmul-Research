import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiPlane428GenFinal
import QiushiPlane453GenFinal
import QiushiPlane464GenFinal
import QiushiStep108Orbit450Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0080 :
    QuotientRankAtLeast (spanCodes [423, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(423, 250), (68, 10), (10, 78)]
    (codeMat 425) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane486GenSource0081 :
    QuotientRankAtLeast (spanCodes [434, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(434, 20), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0082 :
    QuotientRankAtLeast (spanCodes [435, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(435, 30), (68, 78), (10, 68)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0083 :
    QuotientRankAtLeast (spanCodes [436, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(436, 20), (68, 68), (10, 78)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0084 :
    QuotientRankAtLeast (spanCodes [437, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(437, 30), (68, 68), (10, 78)]
    (codeMat 313) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0085 :
    QuotientRankAtLeast (spanCodes [439, 68, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 19, 10] [(439, 19), (68, 78), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step108_orbit450_lb18_unconditional

theorem plane486GenSource0086 :
    QuotientRankAtLeast (spanCodes [68, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(68, 96), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

theorem plane486GenSource0087 :
    QuotientRankAtLeast (spanCodes [65, 10, 5]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(65, 1), (10, 96), (5, 16)]
    (codeMat 141) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

theorem plane486GenSource0088 :
    QuotientRankAtLeast (spanCodes [66, 10, 6]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(66, 113), (10, 112), (6, 16)]
    (codeMat 142) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

theorem plane486GenSource0089 :
    QuotientRankAtLeast (spanCodes [67, 10, 7]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 16, 1] [(67, 113), (10, 112), (7, 16)]
    (codeMat 143) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane428Gen_lb17

end QiushiMatmul
