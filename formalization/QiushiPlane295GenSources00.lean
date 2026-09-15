import QiushiPlane295GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit178Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane295GenSource0000 :
    QuotientRankAtLeast (spanCodes [262, 32, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(262, 100), (32, 1), (22, 33), (10, 42), (1, 63)]
    (codeMat 282) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane295GenSource0001 :
    QuotientRankAtLeast (spanCodes [272, 68, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(272, 272), (68, 68), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane295GenSource0002 :
    QuotientRankAtLeast (spanCodes [272, 70, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 32, 10, 1] [(272, 304), (70, 78), (32, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit178_lb16_wc

theorem plane295GenSource0003 :
    QuotientRankAtLeast (spanCodes [272, 132, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(272, 10), (132, 20), (32, 1), (10, 96), (1, 256)]
    (codeMat 98) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane295GenSource0004 :
    QuotientRankAtLeast (spanCodes [272, 148, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(272, 11), (148, 20), (32, 1), (10, 96), (1, 256)]
    (codeMat 114) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane295GenSource0005 :
    QuotientRankAtLeast (spanCodes [272, 198, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(272, 284), (198, 133), (32, 32), (10, 11), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane295GenSource0006 :
    QuotientRankAtLeast (spanCodes [272, 212, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(272, 316), (212, 142), (32, 32), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane295GenSource0007 :
    QuotientRankAtLeast (spanCodes [272, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(272, 132), (32, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane295GenSource0008 :
    QuotientRankAtLeast (spanCodes [258, 32, 18, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 112), (32, 1), (18, 54), (10, 52), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane295GenSource0009 :
    QuotientRankAtLeast (spanCodes [272, 64, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (64, 128), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
