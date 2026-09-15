import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit212Dispatch
import QiushiWcOrbit214Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 164, 18, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 264), (164, 68), (18, 1), (10, 26), (1, 16)]
    (codeMat 267) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane426GenSource0021 :
    QuotientRankAtLeast (spanCodes [272, 146, 82, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(272, 90), (146, 63), (82, 62), (10, 52), (1, 32)]
    (codeMat 84) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane426GenSource0022 :
    QuotientRankAtLeast (spanCodes [272, 176, 112, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(272, 310), (176, 164), (112, 132), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane426GenSource0023 :
    QuotientRankAtLeast (spanCodes [272, 164, 102, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(272, 350), (164, 175), (102, 142), (10, 10), (1, 1)]
    (codeMat 345) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane426GenSource0024 :
    QuotientRankAtLeast (spanCodes [272, 148, 80, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(272, 287), (148, 126), (80, 31), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane426GenSource0025 :
    QuotientRankAtLeast (spanCodes [272, 150, 82, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(272, 383), (150, 127), (82, 30), (10, 11), (1, 1)]
    (codeMat 337) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane426GenSource0026 :
    QuotientRankAtLeast (spanCodes [272, 166, 98, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 278), (166, 238), (98, 143), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane426GenSource0027 :
    QuotientRankAtLeast (spanCodes [272, 176, 116, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 132, 96, 10, 1] [(272, 413), (176, 238), (116, 106), (10, 10), (1, 1)]
    (codeMat 345) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit212_lb16_wc

theorem plane426GenSource0028 :
    QuotientRankAtLeast (spanCodes [272, 178, 118, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 374), (178, 228), (118, 133), (10, 10), (1, 1)]
    (codeMat 345) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane426GenSource0029 :
    QuotientRankAtLeast (spanCodes [272, 176, 118, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(272, 475), (176, 228), (118, 96), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

end QiushiMatmul
