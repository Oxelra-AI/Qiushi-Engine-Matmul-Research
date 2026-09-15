import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiStep128Mono189From80T
import QiushiWcOrbit127Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0080 :
    QuotientRankAtLeast (spanCodes [145, 68, 33, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(145, 33), (68, 367), (33, 133), (9, 325), (3, 1)]
    (codeMat 185) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane463GenSource0081 :
    QuotientRankAtLeast (spanCodes [144, 67, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(144, 438), (67, 170), (35, 129), (10, 138), (7, 128)]
    (codeMat 459) (codeMat 158) (codeMat 358) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane463GenSource0082 :
    QuotientRankAtLeast (spanCodes [147, 66, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(147, 406), (66, 170), (32, 1), (10, 138), (6, 128)]
    (codeMat 394) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane463GenSource0083 :
    QuotientRankAtLeast (spanCodes [145, 64, 34, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(145, 11), (64, 128), (34, 316), (10, 138), (4, 32)]
    (codeMat 271) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane463GenSource0084 :
    QuotientRankAtLeast (spanCodes [149, 68, 36, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(149, 11), (68, 367), (36, 448), (8, 325), (2, 1)]
    (codeMat 249) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane463GenSource0085 :
    QuotientRankAtLeast (spanCodes [131, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 12, 2, 1] [(131, 109), (68, 274), (32, 2), (16, 1), (10, 13)]
    (codeMat 282) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit127_lb15_wc

theorem plane463GenSource0086 :
    QuotientRankAtLeast (spanCodes [131, 68, 34, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(131, 265), (68, 383), (34, 35), (18, 32), (10, 33)]
    (codeMat 282) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane463GenSource0087 :
    QuotientRankAtLeast (spanCodes [129, 68, 32, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(129, 265), (68, 383), (32, 2), (18, 32), (10, 33)]
    (codeMat 346) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane463GenSource0088 :
    QuotientRankAtLeast (spanCodes [135, 68, 38, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(135, 381), (68, 383), (38, 296), (18, 32), (10, 33)]
    (codeMat 234) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane463GenSource0089 :
    QuotientRankAtLeast (spanCodes [131, 64, 48, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(131, 406), (64, 32), (48, 1), (10, 138), (4, 128)]
    (codeMat 266) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
