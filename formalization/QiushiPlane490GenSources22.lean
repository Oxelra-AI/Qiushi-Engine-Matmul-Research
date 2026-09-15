import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0220 :
    QuotientRankAtLeast (spanCodes [257, 128, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 164), (128, 2), (17, 33), (9, 9), (3, 32)]
    (codeMat 99) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0221 :
    QuotientRankAtLeast (spanCodes [256, 131, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(256, 16), (131, 53), (19, 245), (10, 427), (5, 36)]
    (codeMat 421) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane490GenSource0222 :
    QuotientRankAtLeast (spanCodes [256, 130, 33, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(256, 16), (130, 192), (33, 378), (19, 427), (10, 245)]
    (codeMat 358) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane490GenSource0223 :
    QuotientRankAtLeast (spanCodes [256, 135, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (135, 493), (36, 1), (19, 462), (10, 441)]
    (codeMat 419) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0224 :
    QuotientRankAtLeast (spanCodes [260, 132, 32, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 2), (132, 34), (32, 1), (23, 441), (10, 118)]
    (codeMat 298) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0225 :
    QuotientRankAtLeast (spanCodes [259, 128, 32, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 96), (128, 128), (32, 1), (16, 2), (10, 22), (4, 8)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0226 :
    QuotientRankAtLeast (spanCodes [259, 130, 32, 16, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 232), (130, 128), (32, 3), (16, 2), (10, 20), (6, 8)]
    (codeMat 330) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0227 :
    QuotientRankAtLeast (spanCodes [256, 134, 32, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (134, 34), (32, 1), (19, 441), (10, 119)]
    (codeMat 354) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0228 :
    QuotientRankAtLeast (spanCodes [259, 129, 32, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 96), (129, 232), (32, 1), (16, 3), (10, 30), (4, 8)]
    (codeMat 330) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0229 :
    QuotientRankAtLeast (spanCodes [257, 131, 34, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 252), (131, 224), (34, 10), (18, 8), (10, 136), (6, 3)]
    (codeMat 275) (codeMat 124) (codeMat 124) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
