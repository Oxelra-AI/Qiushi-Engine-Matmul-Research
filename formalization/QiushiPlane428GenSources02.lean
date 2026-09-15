import QiushiPlane428GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit108From29
import QiushiMonoOrbit110From29
import QiushiMonoOrbit134From35T
import QiushiOrbit29FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane428GenSource0020 :
    QuotientRankAtLeast (spanCodes [140, 96, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(140, 84), (96, 160), (16, 8), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

theorem plane428GenSource0021 :
    QuotientRankAtLeast (spanCodes [164, 96, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(164, 96), (96, 228), (16, 9), (2, 1), (1, 3)]
    (codeMat 281) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane428GenSource0022 :
    QuotientRankAtLeast (spanCodes [172, 96, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(172, 98), (96, 237), (16, 9), (2, 1), (1, 3)]
    (codeMat 409) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane428GenSource0023 :
    QuotientRankAtLeast (spanCodes [164, 96, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(164, 228), (96, 68), (16, 3), (8, 1), (2, 24), (1, 8)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane428GenSource0024 :
    QuotientRankAtLeast (spanCodes [298, 96, 16, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [156, 80, 32, 2, 1] [(298, 156), (96, 80), (16, 32), (4, 2), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit134_lb15_mono

theorem plane428GenSource0025 :
    QuotientRankAtLeast (spanCodes [264, 136, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(264, 21), (136, 20), (96, 42), (16, 32), (1, 128)]
    (codeMat 84) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane428GenSource0026 :
    QuotientRankAtLeast (spanCodes [292, 166, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(292, 325), (166, 367), (96, 356), (16, 448), (1, 32)]
    (codeMat 141) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane428GenSource0027 :
    QuotientRankAtLeast (spanCodes [288, 164, 96, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(288, 325), (164, 367), (96, 324), (16, 448), (1, 32)]
    (codeMat 140) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane428GenSource0028 :
    QuotientRankAtLeast (spanCodes [260, 134, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 16), (134, 160), (96, 490), (16, 260), (10, 69), (1, 320)]
    (codeMat 107) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane428GenSource0029 :
    QuotientRankAtLeast (spanCodes [262, 134, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 176), (134, 160), (96, 430), (16, 260), (10, 69), (1, 320)]
    (codeMat 99) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
