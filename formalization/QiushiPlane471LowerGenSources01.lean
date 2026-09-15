import QiushiPlane471LowerGenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiStep128Mono346From214T
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471LowerGenSource0010 :
    QuotientRankAtLeast (spanCodes [258, 68, 35, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(258, 440), (68, 160), (35, 30), (16, 1), (10, 10)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane471LowerGenSource0011 :
    QuotientRankAtLeast (spanCodes [257, 64, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(257, 96), (64, 256), (32, 1), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane471LowerGenSource0012 :
    QuotientRankAtLeast (spanCodes [256, 65, 33, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 1), (65, 32), (33, 42), (21, 175), (10, 341)]
    (codeMat 340) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane471LowerGenSource0013 :
    QuotientRankAtLeast (spanCodes [274, 83, 51, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(274, 280), (83, 170), (51, 30), (10, 21), (7, 1)]
    (codeMat 473) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane471LowerGenSource0014 :
    QuotientRankAtLeast (spanCodes [276, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(276, 476), (84, 477), (53, 440), (10, 424)]
    (codeMat 92) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane471LowerGenSource0015 :
    QuotientRankAtLeast (spanCodes [256, 66, 33, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 32), (66, 132), (33, 42), (22, 464), (10, 133)]
    (codeMat 270) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane471LowerGenSource0016 :
    QuotientRankAtLeast (spanCodes [272, 82, 49, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(272, 268), (82, 191), (49, 10), (10, 21), (6, 1)]
    (codeMat 465) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane471LowerGenSource0017 :
    QuotientRankAtLeast (spanCodes [289, 128, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(289, 100), (128, 16), (84, 477), (10, 424)]
    (codeMat 423) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane471LowerGenSource0018 :
    QuotientRankAtLeast (spanCodes [289, 131, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(289, 30), (131, 262), (83, 160), (10, 434), (7, 1)]
    (codeMat 369) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane471LowerGenSource0019 :
    QuotientRankAtLeast (spanCodes [289, 129, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(289, 11), (129, 434), (80, 278), (10, 132), (4, 1)]
    (codeMat 249) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
