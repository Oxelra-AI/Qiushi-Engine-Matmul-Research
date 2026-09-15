import QiushiGlobalOrbitUnused181Data
import QiushiCertifiedTransport
import QiushiOrbit5FP
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit204Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane181UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [258, 148, 84, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 144, 68, 32, 10, 1] [(258, 386), (148, 68), (84, 212), (32, 455), (10, 312), (1, 32)]
    (codeMat 103) (codeMat 396) (codeMat 106) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc204s4Dispatch

theorem plane181UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [258, 150, 84, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 96, 20, 10, 1] [(258, 96), (150, 400), (84, 181), (32, 192), (10, 507), (1, 292)]
    (codeMat 125) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit82_lb14_unconditional

theorem plane181UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [256, 80, 32, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(256, 64), (80, 160), (32, 8), (8, 16), (4, 1), (2, 4), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

end QiushiMatmul
