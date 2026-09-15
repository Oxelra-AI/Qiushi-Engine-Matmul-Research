import QiushiPlane267GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit134From35T
import QiushiOrbit101FP
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit141Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane267GenSource0000 :
    QuotientRankAtLeast (spanCodes [84, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(84, 84), (32, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane267GenSource0001 :
    QuotientRankAtLeast (spanCodes [68, 32, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(68, 132), (32, 32), (16, 8), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane267GenSource0002 :
    QuotientRankAtLeast (spanCodes [76, 32, 24, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(76, 132), (32, 32), (24, 8), (2, 3), (1, 2)]
    (codeMat 401) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane267GenSource0003 :
    QuotientRankAtLeast (spanCodes [132, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(132, 12), (84, 92), (32, 256), (2, 1), (1, 3)]
    (codeMat 161) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane267GenSource0004 :
    QuotientRankAtLeast (spanCodes [136, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(136, 80), (84, 92), (32, 256), (2, 2), (1, 3)]
    (codeMat 177) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane267GenSource0005 :
    QuotientRankAtLeast (spanCodes [152, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(152, 80), (84, 204), (32, 32), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane267GenSource0006 :
    QuotientRankAtLeast (spanCodes [156, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(156, 204), (84, 156), (32, 32), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane267GenSource0007 :
    QuotientRankAtLeast (spanCodes [264, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(264, 264), (84, 84), (32, 32), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane267GenSource0008 :
    QuotientRankAtLeast (spanCodes [268, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(268, 264), (84, 85), (32, 32), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane267GenSource0009 :
    QuotientRankAtLeast (spanCodes [408, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(408, 408), (84, 84), (32, 32), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
