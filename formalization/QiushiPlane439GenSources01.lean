import QiushiPlane439GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit288From150
import QiushiMonoOrbit340From196
import QiushiStep128Mono343From214
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit166Dispatch
import QiushiWcOrbit178Dispatch
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane439GenSource0010 :
    QuotientRankAtLeast (spanCodes [160, 66, 20, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(160, 341), (66, 68), (20, 42), (12, 10), (1, 1)]
    (codeMat 337) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane439GenSource0011 :
    QuotientRankAtLeast (spanCodes [160, 96, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(160, 274), (96, 258), (20, 100), (1, 1)]
    (codeMat 161) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane439GenSource0012 :
    QuotientRankAtLeast (spanCodes [160, 98, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(160, 374), (98, 359), (20, 100), (1, 1)]
    (codeMat 233) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane439GenSource0013 :
    QuotientRankAtLeast (spanCodes [142, 74, 46, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(142, 117), (74, 11), (46, 329), (20, 97), (1, 1)]
    (codeMat 185) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane439GenSource0014 :
    QuotientRankAtLeast (spanCodes [138, 76, 42, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(138, 164), (76, 316), (42, 11), (20, 42), (1, 32)]
    (codeMat 331) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane439GenSource0015 :
    QuotientRankAtLeast (spanCodes [138, 66, 42, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(138, 21), (66, 11), (42, 352), (20, 97), (1, 1)]
    (codeMat 233) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane439GenSource0016 :
    QuotientRankAtLeast (spanCodes [134, 78, 38, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(134, 294), (78, 11), (38, 386), (20, 262), (1, 1)]
    (codeMat 185) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane439GenSource0017 :
    QuotientRankAtLeast (spanCodes [136, 66, 40, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(136, 20), (66, 10), (40, 256), (20, 97), (1, 1)]
    (codeMat 161) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane439GenSource0018 :
    QuotientRankAtLeast (spanCodes [160, 110, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(160, 315), (110, 335), (20, 101), (1, 1)]
    (codeMat 185) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane439GenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(256, 1), (160, 10), (20, 20), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

end QiushiMatmul
