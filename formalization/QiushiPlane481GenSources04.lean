import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiPlane282GenFinal
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0040 :
    QuotientRankAtLeast (spanCodes [352, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(352, 264), (20, 21), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0041 :
    QuotientRankAtLeast (spanCodes [328, 40, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(328, 68), (40, 1), (20, 42), (1, 32)]
    (codeMat 266) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane481GenSource0042 :
    QuotientRankAtLeast (spanCodes [354, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(354, 266), (20, 21), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0043 :
    QuotientRankAtLeast (spanCodes [356, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(356, 265), (20, 21), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0044 :
    QuotientRankAtLeast (spanCodes [358, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(358, 267), (20, 21), (1, 1)]
    (codeMat 465) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0045 :
    QuotientRankAtLeast (spanCodes [292, 76, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(292, 27), (76, 26), (20, 280), (1, 16)]
    (codeMat 142) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0046 :
    QuotientRankAtLeast (spanCodes [288, 76, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(288, 1), (76, 10), (20, 264), (1, 16)]
    (codeMat 142) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0047 :
    QuotientRankAtLeast (spanCodes [392, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(392, 265), (20, 20), (1, 1)]
    (codeMat 281) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0048 :
    QuotientRankAtLeast (spanCodes [394, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(394, 267), (20, 20), (1, 1)]
    (codeMat 281) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0049 :
    QuotientRankAtLeast (spanCodes [396, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(396, 267), (20, 20), (1, 1)]
    (codeMat 345) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

end QiushiMatmul
