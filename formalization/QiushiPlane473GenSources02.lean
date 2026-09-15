import QiushiPlane473GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane473GenSource0020 :
    QuotientRankAtLeast (spanCodes [256, 129, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(256, 1), (129, 497), (84, 107), (37, 507), (10, 287)]
    (codeMat 188) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane473GenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 129, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 232), (129, 430), (84, 339), (39, 462), (10, 463)]
    (codeMat 443) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane473GenSource0022 :
    QuotientRankAtLeast (spanCodes [260, 134, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(260, 1), (134, 11), (84, 239), (33, 97), (10, 284)]
    (codeMat 461) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane473GenSource0023 :
    QuotientRankAtLeast (spanCodes [278, 148, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(278, 252), (148, 371), (84, 370), (51, 20), (10, 262)]
    (codeMat 212) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane473GenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 145, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(260, 1), (145, 232), (84, 494), (33, 137), (10, 411)]
    (codeMat 117) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane473GenSource0025 :
    QuotientRankAtLeast (spanCodes [262, 147, 84, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(262, 507), (147, 137), (84, 117), (35, 371), (10, 411)]
    (codeMat 375) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane473GenSource0026 :
    QuotientRankAtLeast (spanCodes [259, 135, 69, 38, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(259, 440), (135, 160), (69, 488), (38, 263), (17, 68), (10, 69)]
    (codeMat 107) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane473GenSource0027 :
    QuotientRankAtLeast (spanCodes [293, 162, 71, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(293, 350), (162, 341), (71, 10), (19, 475), (10, 228)]
    (codeMat 236) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane473GenSource0028 :
    QuotientRankAtLeast (spanCodes [260, 147, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(260, 1), (147, 464), (84, 474), (33, 97), (10, 341)]
    (codeMat 397) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane473GenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 151, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(256, 504), (151, 374), (84, 375), (37, 278), (10, 132)]
    (codeMat 157) (codeMat 481) (codeMat 185) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
