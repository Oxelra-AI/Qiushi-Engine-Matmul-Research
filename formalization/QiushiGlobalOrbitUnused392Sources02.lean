import QiushiGlobalOrbitUnused392Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiStep128Mono246From75
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane392UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [259, 164, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 162, 68, 20, 10] [(259, 80), (164, 162), (68, 10), (20, 333), (10, 68)]
    (codeMat 225) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit246_lb16_mono

theorem plane392UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [259, 165, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 162, 68, 20, 10] [(259, 90), (165, 236), (68, 10), (20, 265), (10, 68)]
    (codeMat 169) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit246_lb16_mono

theorem plane392UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [258, 162, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 262), (162, 160), (68, 69), (20, 20), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane392UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 164, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 81), (164, 170), (68, 10), (20, 268), (10, 69), (1, 1)]
    (codeMat 161) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane392UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 256), (160, 160), (64, 64), (16, 16), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
