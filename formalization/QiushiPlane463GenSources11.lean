import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0110 :
    QuotientRankAtLeast (spanCodes [274, 128, 66, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 126), (128, 432), (66, 160), (51, 357), (10, 96), (6, 260)]
    (codeMat 107) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0111 :
    QuotientRankAtLeast (spanCodes [273, 128, 65, 51, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(273, 271), (128, 1), (65, 260), (51, 368), (10, 96), (5, 192)]
    (codeMat 84) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0112 :
    QuotientRankAtLeast (spanCodes [272, 129, 65, 50, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(272, 367), (129, 261), (65, 260), (50, 464), (10, 96), (5, 192)]
    (codeMat 92) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0113 :
    QuotientRankAtLeast (spanCodes [288, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(288, 9), (178, 252), (66, 149), (10, 148), (6, 130), (1, 2)]
    (codeMat 142) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane463GenSource0114 :
    QuotientRankAtLeast (spanCodes [290, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 28), (178, 252), (64, 128), (10, 148), (4, 3), (1, 2)]
    (codeMat 305) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane463GenSource0115 :
    QuotientRankAtLeast (spanCodes [261, 134, 68, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(261, 119), (134, 440), (68, 462), (53, 495), (10, 493)]
    (codeMat 477) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane463GenSource0116 :
    QuotientRankAtLeast (spanCodes [263, 132, 68, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 261), (132, 96), (68, 356), (35, 453), (20, 464), (10, 378)]
    (codeMat 277) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane463GenSource0117 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 32, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(258, 404), (128, 288), (68, 238), (32, 384), (19, 319), (10, 228)]
    (codeMat 183) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane463GenSource0118 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(260, 256), (134, 452), (68, 257), (33, 97), (20, 479), (10, 430)]
    (codeMat 348) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane463GenSource0119 :
    QuotientRankAtLeast (spanCodes [263, 133, 68, 33, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(263, 170), (133, 463), (68, 414), (33, 238), (23, 462), (10, 90)]
    (codeMat 431) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

end QiushiMatmul
