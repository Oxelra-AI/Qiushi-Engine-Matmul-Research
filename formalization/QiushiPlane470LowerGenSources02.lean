import QiushiPlane470LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit311From196
import QiushiStep126Mono175From75
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit216Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470LowerGenSource0020 :
    QuotientRankAtLeast (spanCodes [259, 128, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 96), (128, 1), (80, 10), (10, 31), (4, 256)]
    (codeMat 116) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470LowerGenSource0021 :
    QuotientRankAtLeast (spanCodes [259, 129, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 39), (129, 21), (81, 175), (10, 327), (5, 1)]
    (codeMat 225) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470LowerGenSource0022 :
    QuotientRankAtLeast (spanCodes [259, 130, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 43), (130, 32), (82, 278), (10, 132), (6, 1)]
    (codeMat 169) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane470LowerGenSource0023 :
    QuotientRankAtLeast (spanCodes [259, 129, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(259, 30), (129, 20), (82, 160), (10, 262), (6, 1)]
    (codeMat 225) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane470LowerGenSource0024 :
    QuotientRankAtLeast (spanCodes [259, 131, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 10), (131, 42), (80, 341), (10, 506), (4, 1)]
    (codeMat 481) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane470LowerGenSource0025 :
    QuotientRankAtLeast (spanCodes [259, 144, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(259, 10), (144, 384), (84, 395), (10, 480)]
    (codeMat 165) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane470LowerGenSource0026 :
    QuotientRankAtLeast (spanCodes [259, 128, 69, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 263), (128, 1), (69, 387), (17, 268), (10, 300)]
    (codeMat 348) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane470LowerGenSource0027 :
    QuotientRankAtLeast (spanCodes [259, 129, 71, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 338), (129, 21), (71, 186), (19, 20), (10, 50)]
    (codeMat 207) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470LowerGenSource0028 :
    QuotientRankAtLeast (spanCodes [259, 128, 71, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(259, 327), (128, 1), (71, 451), (19, 333), (10, 97)]
    (codeMat 340) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane470LowerGenSource0029 :
    QuotientRankAtLeast (spanCodes [259, 134, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 132), (134, 387), (65, 1), (21, 175), (10, 269)]
    (codeMat 309) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

end QiushiMatmul
