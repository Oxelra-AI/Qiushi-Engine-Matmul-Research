import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiPlane282GenFinal
import QiushiStep126Mono253From96
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0060 :
    QuotientRankAtLeast (spanCodes [460, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(460, 266), (20, 21), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0061 :
    QuotientRankAtLeast (spanCodes [462, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(462, 264), (20, 21), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0062 :
    QuotientRankAtLeast (spanCodes [480, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(480, 287), (20, 21), (1, 1)]
    (codeMat 473) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0063 :
    QuotientRankAtLeast (spanCodes [482, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(482, 285), (20, 21), (1, 1)]
    (codeMat 473) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0064 :
    QuotientRankAtLeast (spanCodes [456, 42, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(456, 100), (42, 10), (20, 43), (1, 32)]
    (codeMat 267) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane481GenSource0065 :
    QuotientRankAtLeast (spanCodes [484, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(484, 284), (20, 21), (1, 1)]
    (codeMat 409) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0066 :
    QuotientRankAtLeast (spanCodes [486, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(486, 286), (20, 21), (1, 1)]
    (codeMat 409) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0067 :
    QuotientRankAtLeast (spanCodes [420, 78, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(420, 265), (78, 10), (20, 264), (1, 16)]
    (codeMat 206) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0068 :
    QuotientRankAtLeast (spanCodes [418, 78, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(418, 259), (78, 26), (20, 280), (1, 16)]
    (codeMat 206) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0069 :
    QuotientRankAtLeast (spanCodes [128, 20, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 8, 2, 1] [(128, 8), (20, 68), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit253_lb16_mono

end QiushiMatmul
