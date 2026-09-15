import QiushiPlane439GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit347From150
import QiushiMonoOrbit370From196
import QiushiStep128Mono344From201T
import QiushiStep128Mono348From201
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane439GenSource0030 :
    QuotientRankAtLeast (spanCodes [264, 160, 74, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(264, 441), (160, 343), (74, 11), (20, 133), (1, 1)]
    (codeMat 249) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane439GenSource0031 :
    QuotientRankAtLeast (spanCodes [270, 160, 76, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(270, 143), (160, 287), (76, 10), (20, 507), (1, 1)]
    (codeMat 377) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane439GenSource0032 :
    QuotientRankAtLeast (spanCodes [298, 160, 104, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(298, 116), (160, 274), (104, 20), (20, 137), (1, 1)]
    (codeMat 273) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane439GenSource0033 :
    QuotientRankAtLeast (spanCodes [324, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(324, 17), (160, 228), (20, 259), (1, 1)]
    (codeMat 169) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane439GenSource0034 :
    QuotientRankAtLeast (spanCodes [256, 160, 70, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(256, 1), (160, 10), (70, 96), (20, 31), (1, 256)]
    (codeMat 116) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane439GenSource0035 :
    QuotientRankAtLeast (spanCodes [302, 160, 104, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(302, 116), (160, 338), (104, 21), (20, 137), (1, 1)]
    (codeMat 337) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane439GenSource0036 :
    QuotientRankAtLeast (spanCodes [258, 160, 74, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 434), (160, 278), (74, 11), (20, 132), (1, 1)]
    (codeMat 249) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane439GenSource0037 :
    QuotientRankAtLeast (spanCodes [330, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(330, 498), (160, 228), (20, 263), (1, 1)]
    (codeMat 185) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane439GenSource0038 :
    QuotientRankAtLeast (spanCodes [332, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(332, 503), (160, 100), (20, 402), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane439GenSource0039 :
    QuotientRankAtLeast (spanCodes [334, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(334, 334), (160, 160), (20, 20), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

end QiushiMatmul
