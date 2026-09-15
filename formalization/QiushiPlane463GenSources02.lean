import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit204Dispatch
import QiushiWcOrbit218Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0020 :
    QuotientRankAtLeast (spanCodes [261, 165, 68, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(261, 475), (165, 443), (68, 228), (22, 97), (10, 341)]
    (codeMat 279) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane463GenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 167, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(256, 1), (167, 106), (68, 10), (20, 441), (10, 238)]
    (codeMat 492) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane463GenSource0022 :
    QuotientRankAtLeast (spanCodes [257, 166, 68, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(257, 11), (166, 132), (68, 10), (21, 441), (10, 238)]
    (codeMat 421) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane463GenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 165, 68, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(258, 466), (165, 142), (68, 228), (22, 343), (10, 238)]
    (codeMat 375) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane463GenSource0024 :
    QuotientRankAtLeast (spanCodes [257, 167, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(257, 11), (167, 142), (68, 10), (20, 343), (10, 238)]
    (codeMat 485) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane463GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 167, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(258, 274), (167, 486), (68, 493), (20, 176), (10, 424)]
    (codeMat 87) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane463GenSource0026 :
    QuotientRankAtLeast (spanCodes [259, 166, 68, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(259, 255), (166, 78), (68, 493), (21, 176), (10, 424)]
    (codeMat 86) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane463GenSource0027 :
    QuotientRankAtLeast (spanCodes [257, 165, 68, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(257, 68), (165, 486), (68, 69), (22, 176), (10, 424)]
    (codeMat 85) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane463GenSource0028 :
    QuotientRankAtLeast (spanCodes [262, 149, 68, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 363), (149, 97), (68, 30), (38, 362), (10, 383)]
    (codeMat 470) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0029 :
    QuotientRankAtLeast (spanCodes [263, 148, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(263, 126), (148, 11), (68, 353), (39, 127), (10, 383)]
    (codeMat 254) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
