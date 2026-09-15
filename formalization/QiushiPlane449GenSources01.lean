import QiushiPlane449GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit311From196
import QiushiMonoOrbit340From196
import QiushiStep126Mono175From75
import QiushiStep128Mono344From201T
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane449GenSource0010 :
    QuotientRankAtLeast (spanCodes [290, 160, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(290, 31), (160, 11), (16, 1), (14, 96), (1, 256)]
    (codeMat 98) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane449GenSource0011 :
    QuotientRankAtLeast (spanCodes [290, 160, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(290, 434), (160, 180), (20, 20), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane449GenSource0012 :
    QuotientRankAtLeast (spanCodes [286, 130, 34, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(286, 116), (130, 1), (34, 386), (1, 16)]
    (codeMat 205) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane449GenSource0013 :
    QuotientRankAtLeast (spanCodes [280, 132, 36, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(280, 100), (132, 503), (36, 1), (1, 16)]
    (codeMat 395) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane449GenSource0014 :
    QuotientRankAtLeast (spanCodes [276, 136, 40, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(276, 100), (136, 503), (40, 1), (1, 16)]
    (codeMat 458) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane449GenSource0015 :
    QuotientRankAtLeast (spanCodes [276, 134, 38, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(276, 341), (134, 506), (38, 42), (14, 10), (1, 1)]
    (codeMat 401) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane449GenSource0016 :
    QuotientRankAtLeast (spanCodes [278, 138, 42, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(278, 100), (138, 386), (42, 487), (1, 16)]
    (codeMat 335) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane449GenSource0017 :
    QuotientRankAtLeast (spanCodes [274, 132, 36, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(274, 10), (132, 20), (36, 1), (10, 352), (1, 256)]
    (codeMat 99) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane449GenSource0018 :
    QuotientRankAtLeast (spanCodes [270, 146, 50, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(270, 359), (146, 1), (50, 258), (1, 16)]
    (codeMat 143) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane449GenSource0019 :
    QuotientRankAtLeast (spanCodes [266, 150, 54, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(266, 491), (150, 96), (54, 1), (1, 384)]
    (codeMat 115) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

end QiushiMatmul
