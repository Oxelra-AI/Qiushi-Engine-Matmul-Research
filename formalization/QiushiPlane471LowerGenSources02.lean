import QiushiPlane471LowerGenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiStep126Mono245From75
import QiushiStep128Mono346From214T
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit216Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471LowerGenSource0020 :
    QuotientRankAtLeast (spanCodes [289, 129, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(289, 97), (129, 31), (83, 10), (10, 20), (7, 256)]
    (codeMat 94) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane471LowerGenSource0021 :
    QuotientRankAtLeast (spanCodes [289, 129, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(289, 43), (129, 464), (82, 175), (10, 341), (6, 32)]
    (codeMat 334) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane471LowerGenSource0022 :
    QuotientRankAtLeast (spanCodes [289, 129, 69, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(289, 278), (129, 42), (69, 175), (17, 10), (10, 11)]
    (codeMat 395) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane471LowerGenSource0023 :
    QuotientRankAtLeast (spanCodes [289, 129, 71, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(289, 133), (129, 332), (71, 238), (19, 333), (10, 300)]
    (codeMat 415) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane471LowerGenSource0024 :
    QuotientRankAtLeast (spanCodes [289, 131, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(289, 422), (131, 21), (68, 170), (16, 1), (10, 10)]
    (codeMat 458) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane471LowerGenSource0025 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(289, 262), (129, 10), (64, 1), (20, 170), (10, 21)]
    (codeMat 396) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane471LowerGenSource0026 :
    QuotientRankAtLeast (spanCodes [289, 145, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(289, 10), (145, 42), (80, 464), (10, 133), (4, 1)]
    (codeMat 177) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane471LowerGenSource0027 :
    QuotientRankAtLeast (spanCodes [289, 131, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(289, 262), (131, 11), (65, 1), (21, 191), (10, 21)]
    (codeMat 397) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane471LowerGenSource0028 :
    QuotientRankAtLeast (spanCodes [289, 151, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(289, 100), (151, 101), (84, 117), (10, 424)]
    (codeMat 431) (codeMat 500) (codeMat 94) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

theorem plane471LowerGenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 131, 84, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 161, 68, 20, 10] [(258, 80), (131, 328), (84, 161), (35, 322), (10, 68)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit245_lb16_mono

end QiushiMatmul
