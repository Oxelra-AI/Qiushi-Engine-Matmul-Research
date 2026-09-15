import QiushiPlane439GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit340From196
import QiushiMonoOrbit347From150
import QiushiMonoOrbit370From196
import QiushiStep126Mono323From220
import QiushiStep128Mono344From201T
import QiushiStep128Mono348From201
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane439GenSource0040 :
    QuotientRankAtLeast (spanCodes [352, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(352, 503), (160, 487), (20, 259), (1, 1)]
    (codeMat 225) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane439GenSource0041 :
    QuotientRankAtLeast (spanCodes [262, 160, 100, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 21), (160, 175), (100, 137), (20, 327), (1, 1)]
    (codeMat 233) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane439GenSource0042 :
    QuotientRankAtLeast (spanCodes [256, 160, 100, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(256, 1), (160, 11), (100, 68), (20, 80), (1, 288)]
    (codeMat 212) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane439GenSource0043 :
    QuotientRankAtLeast (spanCodes [358, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(358, 359), (160, 374), (20, 274), (1, 16)]
    (codeMat 205) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane439GenSource0044 :
    QuotientRankAtLeast (spanCodes [360, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(360, 1), (160, 502), (20, 402), (1, 16)]
    (codeMat 206) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane439GenSource0045 :
    QuotientRankAtLeast (spanCodes [362, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(362, 506), (160, 180), (20, 20), (1, 1)]
    (codeMat 345) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane439GenSource0046 :
    QuotientRankAtLeast (spanCodes [364, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 228, 16, 1] [(364, 17), (160, 483), (20, 263), (1, 1)]
    (codeMat 249) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit348_lb16_mono

theorem plane439GenSource0047 :
    QuotientRankAtLeast (spanCodes [262, 160, 104, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 327), (160, 175), (104, 353), (20, 509), (1, 1)]
    (codeMat 377) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane439GenSource0048 :
    QuotientRankAtLeast (spanCodes [160, 18, 8, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(160, 166), (18, 2), (8, 9), (6, 32), (1, 8)]
    (codeMat 331) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane439GenSource0049 :
    QuotientRankAtLeast (spanCodes [132, 36, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 36, 16, 1] [(132, 209), (36, 1), (20, 17), (1, 36)]
    (codeMat 403) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit323_lb15_mono

end QiushiMatmul
