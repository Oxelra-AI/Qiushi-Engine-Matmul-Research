import QiushiPlane298GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit174From65
import QiushiMonoOrbit192From65
import QiushiMonoOrbit195From65
import QiushiMonoOrbit199From69
import QiushiStep128Mono189From80T
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit185Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane298GenSource0010 :
    QuotientRankAtLeast (spanCodes [276, 148, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(276, 11), (148, 43), (32, 1), (10, 126), (1, 432)]
    (codeMat 298) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane298GenSource0011 :
    QuotientRankAtLeast (spanCodes [278, 150, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 132, 32, 10, 1] [(278, 306), (150, 132), (32, 32), (10, 10), (1, 1)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit195_lb15_mono

theorem plane298GenSource0012 :
    QuotientRankAtLeast (spanCodes [324, 196, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(324, 324), (196, 132), (32, 32), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane298GenSource0013 :
    QuotientRankAtLeast (spanCodes [326, 198, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(326, 10), (198, 11), (32, 438), (10, 284), (1, 32)]
    (codeMat 460) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane298GenSource0014 :
    QuotientRankAtLeast (spanCodes [336, 208, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(336, 373), (208, 138), (32, 32), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane298GenSource0015 :
    QuotientRankAtLeast (spanCodes [338, 210, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(338, 413), (210, 43), (32, 128), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane298GenSource0016 :
    QuotientRankAtLeast (spanCodes [340, 212, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 132, 32, 10, 1] [(340, 369), (212, 142), (32, 32), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit199_lb15_mono

theorem plane298GenSource0017 :
    QuotientRankAtLeast (spanCodes [342, 214, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 20, 10, 1] [(342, 271), (214, 270), (32, 260), (10, 160), (1, 432)]
    (codeMat 156) (codeMat 460) (codeMat 122) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit174_lb15_mono

theorem plane298GenSource0018 :
    QuotientRankAtLeast (spanCodes [384, 32, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(384, 2), (32, 256), (10, 97), (6, 1), (1, 8)]
    (codeMat 161) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane298GenSource0019 :
    QuotientRankAtLeast (spanCodes [384, 32, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(384, 2), (32, 9), (16, 8), (10, 96), (1, 256)]
    (codeMat 98) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

end QiushiMatmul
