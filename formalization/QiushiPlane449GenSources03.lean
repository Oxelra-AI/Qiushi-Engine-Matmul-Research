import QiushiPlane449GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit311From196
import QiushiMonoOrbit340From196
import QiushiStep126Mono175From75
import QiushiStep128Mono344From201T
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit212Dispatch
import QiushiWcOrbit213Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane449GenSource0030 :
    QuotientRankAtLeast (spanCodes [296, 160, 66, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 132, 96, 10, 1] [(296, 503), (160, 406), (66, 10), (20, 132), (1, 1)]
    (codeMat 225) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit212_lb16_wc

theorem plane449GenSource0031 :
    QuotientRankAtLeast (spanCodes [290, 160, 70, 30, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(290, 263), (160, 280), (70, 11), (30, 435), (1, 1)]
    (codeMat 417) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane449GenSource0032 :
    QuotientRankAtLeast (spanCodes [316, 160, 90, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(316, 11), (160, 490), (90, 96), (1, 384)]
    (codeMat 213) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane449GenSource0033 :
    QuotientRankAtLeast (spanCodes [316, 160, 92, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(316, 101), (160, 259), (92, 359), (1, 16)]
    (codeMat 396) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane449GenSource0034 :
    QuotientRankAtLeast (spanCodes [296, 160, 74, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(296, 96), (160, 400), (74, 10), (20, 132), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane449GenSource0035 :
    QuotientRankAtLeast (spanCodes [316, 160, 96, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(316, 502), (160, 387), (96, 386), (1, 16)]
    (codeMat 140) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane449GenSource0036 :
    QuotientRankAtLeast (spanCodes [316, 160, 100, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(316, 387), (160, 101), (100, 487), (1, 16)]
    (codeMat 270) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane449GenSource0037 :
    QuotientRankAtLeast (spanCodes [286, 130, 68, 34, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(286, 340), (130, 32), (68, 11), (34, 132), (1, 1)]
    (codeMat 169) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane449GenSource0038 :
    QuotientRankAtLeast (spanCodes [274, 142, 70, 46, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(274, 276), (142, 106), (70, 10), (46, 506), (1, 1)]
    (codeMat 417) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane449GenSource0039 :
    QuotientRankAtLeast (spanCodes [274, 142, 68, 46, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(274, 287), (142, 142), (68, 10), (46, 96), (1, 1)]
    (codeMat 233) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

end QiushiMatmul
