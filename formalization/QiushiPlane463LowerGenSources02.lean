import QiushiPlane463LowerGenData
import QiushiCertifiedTransport
import QiushiStep128Mono160From75
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit202Dispatch
import QiushiWcOrbit204Dispatch
import QiushiWcOrbit218Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463LowerGenSource0020 :
    QuotientRankAtLeast (spanCodes [262, 178, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 20, 10, 1] [(262, 258), (178, 278), (68, 68), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit160_lb16_mono

theorem plane463LowerGenSource0021 :
    QuotientRankAtLeast (spanCodes [259, 160, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 10, 1] [(259, 411), (160, 10), (68, 228), (19, 400), (10, 160)]
    (codeMat 86) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit202_lb16_wc

theorem plane463LowerGenSource0022 :
    QuotientRankAtLeast (spanCodes [258, 160, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 10, 1] [(258, 383), (160, 170), (68, 228), (19, 400), (10, 160)]
    (codeMat 87) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit202_lb16_wc

theorem plane463LowerGenSource0023 :
    QuotientRankAtLeast (spanCodes [257, 160, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 10, 1] [(257, 69), (160, 170), (68, 68), (19, 400), (10, 160)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit202_lb16_wc

theorem plane463LowerGenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 10, 1] [(256, 1), (160, 10), (68, 68), (19, 400), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit202_lb16_wc

theorem plane463LowerGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 167, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(256, 1), (167, 106), (68, 10), (20, 441), (10, 238)]
    (codeMat 492) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane463LowerGenSource0026 :
    QuotientRankAtLeast (spanCodes [256, 166, 68, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(256, 1), (166, 96), (68, 10), (21, 343), (10, 238)]
    (codeMat 428) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane463LowerGenSource0027 :
    QuotientRankAtLeast (spanCodes [258, 167, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(258, 274), (167, 486), (68, 493), (20, 176), (10, 424)]
    (codeMat 87) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane463LowerGenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(256, 1), (164, 78), (68, 69), (23, 176), (10, 424)]
    (codeMat 84) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane463LowerGenSource0029 :
    QuotientRankAtLeast (spanCodes [262, 149, 68, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 363), (149, 97), (68, 30), (38, 362), (10, 383)]
    (codeMat 470) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
