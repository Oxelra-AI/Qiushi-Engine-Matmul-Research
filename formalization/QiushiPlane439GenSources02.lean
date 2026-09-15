import QiushiPlane439GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit288From150
import QiushiMonoOrbit340From196
import QiushiMonoOrbit342From196
import QiushiStep126Mono175From75
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane439GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [296, 100, 16, 1] [(258, 333), (160, 100), (20, 296), (1, 16)]
    (codeMat 143) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit342_lb16_mono

theorem plane439GenSource0021 :
    QuotientRankAtLeast (spanCodes [262, 160, 20, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 133), (160, 341), (20, 42), (12, 10), (1, 1)]
    (codeMat 337) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane439GenSource0022 :
    QuotientRankAtLeast (spanCodes [262, 160, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(262, 262), (160, 160), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane439GenSource0023 :
    QuotientRankAtLeast (spanCodes [266, 136, 40, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(266, 340), (136, 132), (40, 1), (20, 42), (1, 32)]
    (codeMat 266) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane439GenSource0024 :
    QuotientRankAtLeast (spanCodes [292, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [296, 100, 16, 1] [(292, 1), (160, 332), (20, 296), (1, 16)]
    (codeMat 207) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit342_lb16_mono

theorem plane439GenSource0025 :
    QuotientRankAtLeast (spanCodes [294, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(294, 31), (160, 30), (20, 20), (1, 256)]
    (codeMat 93) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

theorem plane439GenSource0026 :
    QuotientRankAtLeast (spanCodes [262, 142, 46, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 509), (142, 156), (46, 51), (20, 21), (1, 1)]
    (codeMat 473) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane439GenSource0027 :
    QuotientRankAtLeast (spanCodes [262, 138, 42, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 464), (138, 164), (42, 11), (20, 42), (1, 32)]
    (codeMat 331) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane439GenSource0028 :
    QuotientRankAtLeast (spanCodes [320, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(320, 1), (160, 100), (20, 274), (1, 16)]
    (codeMat 140) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane439GenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 160, 66, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(256, 1), (160, 10), (66, 96), (20, 20), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
