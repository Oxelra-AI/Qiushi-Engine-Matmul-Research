import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiStep128Mono189From80T
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0070 :
    QuotientRankAtLeast (spanCodes [262, 194, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(262, 138), (194, 422), (36, 1), (16, 128), (1, 390)]
    (codeMat 171) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane427GenSource0071 :
    QuotientRankAtLeast (spanCodes [320, 132, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(320, 32), (132, 138), (36, 128), (16, 1), (1, 390)]
    (codeMat 226) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane427GenSource0072 :
    QuotientRankAtLeast (spanCodes [332, 136, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(332, 422), (136, 11), (36, 390), (16, 1), (1, 128)]
    (codeMat 114) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane427GenSource0073 :
    QuotientRankAtLeast (spanCodes [384, 68, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(384, 32), (68, 10), (36, 128), (16, 390), (1, 1)]
    (codeMat 225) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane427GenSource0074 :
    QuotientRankAtLeast (spanCodes [266, 204, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(266, 116), (204, 468), (36, 1), (16, 511), (1, 384)]
    (codeMat 355) (codeMat 214) (codeMat 214) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane427GenSource0075 :
    QuotientRankAtLeast (spanCodes [322, 132, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(322, 11), (132, 138), (36, 438), (16, 32), (1, 128)]
    (codeMat 141) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane427GenSource0076 :
    QuotientRankAtLeast (spanCodes [330, 140, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(330, 84), (140, 500), (36, 511), (16, 1), (1, 384)]
    (codeMat 354) (codeMat 358) (codeMat 158) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane427GenSource0077 :
    QuotientRankAtLeast (spanCodes [334, 136, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(334, 171), (136, 284), (36, 128), (16, 32), (1, 438)]
    (codeMat 157) (codeMat 345) (codeMat 345) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane427GenSource0078 :
    QuotientRankAtLeast (spanCodes [392, 78, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(392, 42), (78, 11), (36, 384), (16, 511), (1, 1)]
    (codeMat 369) (codeMat 403) (codeMat 403) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane427GenSource0079 :
    QuotientRankAtLeast (spanCodes [394, 76, 36, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(394, 317), (76, 284), (36, 438), (16, 128), (1, 32)]
    (codeMat 85) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
