import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit178Dispatch
import QiushiWcOrbit214Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0000 :
    QuotientRankAtLeast (spanCodes [260, 160, 70, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(260, 32), (160, 283), (70, 10), (10, 78), (1, 1)]
    (codeMat 425) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane315GenSource0001 :
    QuotientRankAtLeast (spanCodes [260, 160, 116, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(260, 504), (160, 228), (116, 106), (10, 10), (1, 1)]
    (codeMat 409) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane315GenSource0002 :
    QuotientRankAtLeast (spanCodes [260, 160, 118, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(260, 504), (160, 238), (118, 132), (10, 10), (1, 1)]
    (codeMat 473) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane315GenSource0003 :
    QuotientRankAtLeast (spanCodes [260, 144, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(260, 438), (144, 128), (48, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane315GenSource0004 :
    QuotientRankAtLeast (spanCodes [260, 146, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(260, 438), (146, 32), (50, 138), (10, 10), (1, 1)]
    (codeMat 465) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane315GenSource0005 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (160, 68), (64, 2), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane315GenSource0006 :
    QuotientRankAtLeast (spanCodes [258, 160, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 139), (160, 252), (64, 3), (10, 148), (6, 130), (1, 2)]
    (codeMat 141) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane315GenSource0007 :
    QuotientRankAtLeast (spanCodes [256, 160, 66, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (160, 104), (66, 20), (10, 148), (4, 1), (1, 2)]
    (codeMat 417) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane315GenSource0008 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (160, 160), (68, 68), (20, 436), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane315GenSource0009 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (160, 160), (68, 68), (16, 16), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
