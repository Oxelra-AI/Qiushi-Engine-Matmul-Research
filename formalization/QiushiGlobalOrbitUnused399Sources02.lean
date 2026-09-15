import QiushiGlobalOrbitUnused399Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane399UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 129, 69, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 280), (129, 160), (69, 80), (37, 91), (20, 228), (10, 274)]
    (codeMat 102) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane399UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [259, 129, 69, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(259, 10), (129, 31), (69, 20), (37, 160), (20, 488), (10, 280)]
    (codeMat 205) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane399UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [262, 129, 69, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 90), (129, 483), (69, 343), (37, 488), (20, 80), (10, 280)]
    (codeMat 159) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane399UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [257, 131, 71, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(257, 502), (131, 274), (71, 429), (39, 21), (20, 31), (10, 20)]
    (codeMat 275) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane399UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 160), (130, 8), (66, 264), (34, 78), (16, 1), (10, 77), (4, 432)]
    (codeMat 298) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
