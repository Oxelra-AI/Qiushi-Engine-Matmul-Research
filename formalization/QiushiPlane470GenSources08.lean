import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiOrbit35FP
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit180Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0080 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 20), (128, 1), (64, 2), (20, 96), (8, 128), (2, 8)]
    (codeMat 140) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0081 :
    QuotientRankAtLeast (spanCodes [256, 149, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [144, 84, 32, 10, 1] [(256, 32), (149, 197), (84, 207), (9, 144), (3, 1)]
    (codeMat 481) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit180_lb15_wc

theorem plane470GenSource0082 :
    QuotientRankAtLeast (spanCodes [259, 146, 81, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(259, 391), (146, 32), (81, 33), (10, 301), (5, 128)]
    (codeMat 125) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane470GenSource0083 :
    QuotientRankAtLeast (spanCodes [257, 149, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(257, 132), (149, 490), (84, 174), (8, 32), (2, 325)]
    (codeMat 277) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane470GenSource0084 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 139), (130, 9), (64, 2), (20, 252), (10, 31), (1, 3)]
    (codeMat 165) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0085 :
    QuotientRankAtLeast (spanCodes [259, 146, 83, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 368), (146, 1), (83, 31), (49, 180), (10, 20), (7, 432)]
    (codeMat 215) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane470GenSource0086 :
    QuotientRankAtLeast (spanCodes [259, 144, 84, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(259, 97), (144, 2), (84, 107), (53, 283), (10, 274)]
    (codeMat 174) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane470GenSource0087 :
    QuotientRankAtLeast (spanCodes [259, 145, 81, 49, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(259, 69), (145, 80), (81, 81), (49, 319), (10, 91), (5, 384)]
    (codeMat 124) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane470GenSource0088 :
    QuotientRankAtLeast (spanCodes [259, 129, 83, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 137), (129, 246), (83, 29), (35, 136), (10, 232), (7, 128)]
    (codeMat 94) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane470GenSource0089 :
    QuotientRankAtLeast (spanCodes [256, 165, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 511), (165, 426), (84, 116), (9, 32), (3, 384)]
    (codeMat 94) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

end QiushiMatmul
