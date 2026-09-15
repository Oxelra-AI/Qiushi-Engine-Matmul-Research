import QiushiPlane428GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit134From35T
import QiushiOrbit35FP
import QiushiStep126Mono323From220
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit119Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane428GenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 132, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 16), (132, 160), (96, 170), (16, 260), (10, 69), (1, 320)]
    (codeMat 99) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane428GenSource0031 :
    QuotientRankAtLeast (spanCodes [416, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 36, 16, 1] [(416, 37), (96, 53), (16, 36), (1, 192)]
    (codeMat 102) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit323_lb15_mono

theorem plane428GenSource0032 :
    QuotientRankAtLeast (spanCodes [296, 142, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(296, 350), (142, 379), (96, 245), (16, 36), (1, 192)]
    (codeMat 111) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane428GenSource0033 :
    QuotientRankAtLeast (spanCodes [292, 140, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(292, 1), (140, 379), (96, 209), (16, 36), (1, 192)]
    (codeMat 111) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane428GenSource0034 :
    QuotientRankAtLeast (spanCodes [298, 128, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(298, 204), (128, 2), (96, 80), (16, 1), (1, 32)]
    (codeMat 98) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane428GenSource0035 :
    QuotientRankAtLeast (spanCodes [302, 130, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(302, 204), (130, 2), (96, 112), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane428GenSource0036 :
    QuotientRankAtLeast (spanCodes [426, 96, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(426, 188), (96, 112), (16, 32), (6, 2), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane428GenSource0037 :
    QuotientRankAtLeast (spanCodes [418, 96, 16, 8, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(418, 245), (96, 148), (16, 130), (8, 2), (6, 9), (1, 1)]
    (codeMat 273) (codeMat 419) (codeMat 183) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane428GenSource0038 :
    QuotientRankAtLeast (spanCodes [256, 72, 40, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(256, 45), (72, 32), (40, 1), (16, 2), (1, 256)]
    (codeMat 114) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane428GenSource0039 :
    QuotientRankAtLeast (spanCodes [264, 64, 32, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(264, 12), (64, 32), (32, 1), (16, 2), (1, 256)]
    (codeMat 98) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

end QiushiMatmul
