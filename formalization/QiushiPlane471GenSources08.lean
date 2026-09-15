import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit165Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0080 :
    QuotientRankAtLeast (spanCodes [256, 84, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(256, 2), (84, 84), (32, 1), (10, 264), (1, 32)]
    (codeMat 98) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane471GenSource0081 :
    QuotientRankAtLeast (spanCodes [256, 84, 33, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(256, 32), (84, 142), (33, 324), (9, 1), (3, 448)]
    (codeMat 99) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane471GenSource0082 :
    QuotientRankAtLeast (spanCodes [257, 80, 32, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 20), (80, 96), (32, 1), (8, 8), (4, 2), (2, 128)]
    (codeMat 266) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0083 :
    QuotientRankAtLeast (spanCodes [257, 80, 32, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 22), (80, 252), (32, 3), (9, 9), (4, 2), (3, 130)]
    (codeMat 267) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0084 :
    QuotientRankAtLeast (spanCodes [260, 84, 37, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(260, 32), (84, 335), (37, 324), (8, 1), (2, 448)]
    (codeMat 106) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane471GenSource0085 :
    QuotientRankAtLeast (spanCodes [258, 80, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 150), (80, 232), (34, 22), (10, 30), (4, 2), (1, 3)]
    (codeMat 401) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0086 :
    QuotientRankAtLeast (spanCodes [261, 64, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(261, 310), (64, 438), (36, 32), (20, 33), (10, 43)]
    (codeMat 346) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane471GenSource0087 :
    QuotientRankAtLeast (spanCodes [256, 70, 33, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(256, 438), (70, 413), (33, 138), (18, 128), (10, 129)]
    (codeMat 474) (codeMat 485) (codeMat 171) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane471GenSource0088 :
    QuotientRankAtLeast (spanCodes [276, 84, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(276, 469), (84, 85), (52, 42), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane471GenSource0089 :
    QuotientRankAtLeast (spanCodes [275, 80, 50, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(275, 331), (80, 308), (50, 321), (10, 97), (4, 1)]
    (codeMat 177) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

end QiushiMatmul
