import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0210 :
    QuotientRankAtLeast (spanCodes [260, 133, 64, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (133, 287), (64, 9), (37, 105), (20, 414), (9, 8), (3, 130)]
    (codeMat 415) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0211 :
    QuotientRankAtLeast (spanCodes [261, 132, 64, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 138), (132, 235), (64, 8), (36, 3), (20, 363), (9, 1), (3, 511)]
    (codeMat 419) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0212 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 23), (128, 3), (64, 2), (32, 511), (20, 227), (9, 130), (3, 8)]
    (codeMat 460) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0213 :
    QuotientRankAtLeast (spanCodes [256, 132, 69, 33, 17, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (132, 227), (69, 503), (33, 385), (17, 386), (9, 384), (3, 130)]
    (codeMat 234) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0214 :
    QuotientRankAtLeast (spanCodes [272, 128, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 227), (128, 511), (81, 21), (49, 352), (9, 360), (5, 384), (3, 128)]
    (codeMat 87) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0215 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 33, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (144, 511), (81, 287), (33, 129), (9, 3), (5, 128), (3, 256)]
    (codeMat 99) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0216 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 36, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (132, 362), (65, 1), (36, 130), (21, 227), (8, 8), (2, 511)]
    (codeMat 405) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0217 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (129, 68), (64, 1), (32, 16), (20, 160), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0218 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 36, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (129, 276), (68, 503), (36, 1), (16, 128), (8, 384), (2, 130)]
    (codeMat 171) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0219 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 33, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 284), (132, 97), (68, 227), (33, 28), (16, 1), (8, 3), (2, 8)]
    (codeMat 394) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
