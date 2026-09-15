import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit165Dispatch
import QiushiWcOrbit179Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0090 :
    QuotientRankAtLeast (spanCodes [289, 132, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(289, 42), (132, 222), (84, 84), (9, 128), (3, 1)]
    (codeMat 241) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit179_lb15_wc

theorem plane471GenSource0091 :
    QuotientRankAtLeast (spanCodes [289, 133, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(289, 132), (133, 490), (84, 142), (8, 32), (2, 325)]
    (codeMat 407) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane471GenSource0092 :
    QuotientRankAtLeast (spanCodes [288, 134, 84, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(288, 2), (134, 381), (84, 84), (10, 296), (1, 32)]
    (codeMat 142) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane471GenSource0093 :
    QuotientRankAtLeast (spanCodes [289, 132, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(289, 20), (132, 97), (64, 130), (20, 96), (8, 128), (2, 8)]
    (codeMat 142) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0094 :
    QuotientRankAtLeast (spanCodes [289, 145, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(289, 132), (145, 324), (84, 491), (9, 32), (3, 325)]
    (codeMat 415) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane471GenSource0095 :
    QuotientRankAtLeast (spanCodes [289, 133, 65, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(289, 20), (133, 235), (65, 130), (21, 232), (9, 128), (3, 8)]
    (codeMat 206) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0096 :
    QuotientRankAtLeast (spanCodes [288, 132, 66, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 128), (132, 246), (66, 29), (22, 255), (10, 31), (1, 3)]
    (codeMat 183) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane471GenSource0097 :
    QuotientRankAtLeast (spanCodes [289, 148, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(289, 21), (148, 10), (84, 298), (8, 320), (2, 1)]
    (codeMat 177) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane471GenSource0098 :
    QuotientRankAtLeast (spanCodes [289, 135, 68, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(289, 139), (135, 43), (68, 413), (16, 32), (10, 284)]
    (codeMat 190) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane471GenSource0099 :
    QuotientRankAtLeast (spanCodes [256, 128, 84, 33, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 3), (128, 2), (84, 87), (33, 411), (10, 493)]
    (codeMat 124) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
