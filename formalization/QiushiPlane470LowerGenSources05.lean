import QiushiPlane470LowerGenData
import QiushiCertifiedTransport
import QiushiStep99Mono3032
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470LowerGenSource0050 :
    QuotientRankAtLeast (spanCodes [259, 133, 84, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(259, 269), (133, 139), (84, 396), (53, 294), (10, 295)]
    (codeMat 443) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane470LowerGenSource0051 :
    QuotientRankAtLeast (spanCodes [256, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(256, 256), (68, 68), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

end QiushiMatmul
