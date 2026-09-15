import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiPlane282GenFinal
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0050 :
    QuotientRankAtLeast (spanCodes [398, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(398, 265), (20, 20), (1, 1)]
    (codeMat 345) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0051 :
    QuotientRankAtLeast (spanCodes [424, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(424, 287), (20, 20), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0052 :
    QuotientRankAtLeast (spanCodes [426, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(426, 285), (20, 20), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0053 :
    QuotientRankAtLeast (spanCodes [392, 34, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(392, 100), (34, 10), (20, 11), (1, 32)]
    (codeMat 267) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane481GenSource0054 :
    QuotientRankAtLeast (spanCodes [428, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(428, 285), (20, 20), (1, 1)]
    (codeMat 409) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0055 :
    QuotientRankAtLeast (spanCodes [430, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(430, 287), (20, 20), (1, 1)]
    (codeMat 409) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0056 :
    QuotientRankAtLeast (spanCodes [390, 70, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(390, 27), (70, 26), (20, 280), (1, 16)]
    (codeMat 204) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0057 :
    QuotientRankAtLeast (spanCodes [384, 70, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(384, 1), (70, 10), (20, 264), (1, 16)]
    (codeMat 204) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0058 :
    QuotientRankAtLeast (spanCodes [456, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(456, 265), (20, 21), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0059 :
    QuotientRankAtLeast (spanCodes [458, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(458, 267), (20, 21), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

end QiushiMatmul
