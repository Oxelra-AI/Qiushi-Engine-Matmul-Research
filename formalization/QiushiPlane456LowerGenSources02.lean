import QiushiPlane456LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit370From196
import QiushiStep126Mono159From75
import QiushiStep128Mono343From214
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456LowerGenSource0020 :
    QuotientRankAtLeast (spanCodes [257, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(257, 137), (130, 1), (35, 175), (20, 21), (10, 509)]
    (codeMat 397) (codeMat 111) (codeMat 412) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane456LowerGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 129, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10, 1] [(258, 80), (129, 160), (32, 1), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit159_lb16_mono

theorem plane456LowerGenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 32), (130, 1), (35, 341), (20, 42), (10, 133)]
    (codeMat 277) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 132, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 1), (132, 10), (37, 133), (20, 42), (10, 341)]
    (codeMat 396) (codeMat 85) (codeMat 340) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0024 :
    QuotientRankAtLeast (spanCodes [259, 132, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 350), (132, 43), (37, 383), (20, 42), (10, 506)]
    (codeMat 478) (codeMat 111) (codeMat 412) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0025 :
    QuotientRankAtLeast (spanCodes [261, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(261, 164), (130, 32), (35, 175), (20, 42), (10, 464)]
    (codeMat 334) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0026 :
    QuotientRankAtLeast (spanCodes [295, 161, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(295, 347), (161, 346), (20, 21), (10, 495)]
    (codeMat 285) (codeMat 117) (codeMat 380) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane456LowerGenSource0027 :
    QuotientRankAtLeast (spanCodes [320, 161, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(320, 1), (161, 116), (20, 350), (10, 315)]
    (codeMat 380) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

theorem plane456LowerGenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 161, 65, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(256, 1), (161, 499), (65, 504), (20, 132), (10, 278)]
    (codeMat 212) (codeMat 206) (codeMat 498) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456LowerGenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 161, 67, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(258, 472), (161, 239), (67, 96), (20, 316), (10, 97)]
    (codeMat 335) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

end QiushiMatmul
