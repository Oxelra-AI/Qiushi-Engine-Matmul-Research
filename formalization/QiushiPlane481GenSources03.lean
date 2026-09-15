import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit442From373
import QiushiMonoOrbit443From373
import QiushiPlane282GenFinal
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0030 :
    QuotientRankAtLeast (spanCodes [264, 32, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(264, 68), (32, 1), (20, 10), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane481GenSource0031 :
    QuotientRankAtLeast (spanCodes [298, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(298, 266), (20, 20), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0032 :
    QuotientRankAtLeast (spanCodes [300, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(300, 264), (20, 20), (1, 1)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0033 :
    QuotientRankAtLeast (spanCodes [302, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(302, 266), (20, 20), (1, 1)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0034 :
    QuotientRankAtLeast (spanCodes [260, 68, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(260, 27), (68, 26), (20, 280), (1, 16)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0035 :
    QuotientRankAtLeast (spanCodes [256, 68, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(256, 1), (68, 10), (20, 264), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane481GenSource0036 :
    QuotientRankAtLeast (spanCodes [328, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(328, 264), (20, 21), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0037 :
    QuotientRankAtLeast (spanCodes [330, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(330, 266), (20, 21), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane481GenSource0038 :
    QuotientRankAtLeast (spanCodes [332, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 20, 1] [(332, 265), (20, 21), (1, 1)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit442_lb17_mono

theorem plane481GenSource0039 :
    QuotientRankAtLeast (spanCodes [334, 20, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(334, 267), (20, 21), (1, 1)]
    (codeMat 337) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

end QiushiMatmul
