import QiushiPlane481GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit35FP
import QiushiStep99Orbit120Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane481GenSource0080 :
    QuotientRankAtLeast (spanCodes [290, 172, 96, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(290, 43), (172, 143), (96, 507), (20, 373), (1, 32)]
    (codeMat 334) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane481GenSource0081 :
    QuotientRankAtLeast (spanCodes [294, 132, 76, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(294, 62), (132, 113), (76, 52), (20, 112), (1, 32)]
    (codeMat 142) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane481GenSource0082 :
    QuotientRankAtLeast (spanCodes [66, 42, 18, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(66, 133), (42, 33), (18, 40), (6, 3), (1, 2)]
    (codeMat 281) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane481GenSource0083 :
    QuotientRankAtLeast (spanCodes [160, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 224), (96, 96), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0084 :
    QuotientRankAtLeast (spanCodes [164, 100, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(164, 246), (100, 118), (20, 30), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0085 :
    QuotientRankAtLeast (spanCodes [162, 98, 20, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(162, 118), (98, 116), (20, 265), (12, 264), (1, 32)]
    (codeMat 98) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane481GenSource0086 :
    QuotientRankAtLeast (spanCodes [134, 70, 20, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(134, 175), (70, 135), (20, 166), (14, 132), (1, 2)]
    (codeMat 207) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane481GenSource0087 :
    QuotientRankAtLeast (spanCodes [132, 68, 20, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(132, 287), (68, 284), (20, 306), (14, 272), (1, 32)]
    (codeMat 95) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane481GenSource0088 :
    QuotientRankAtLeast (spanCodes [128, 100, 20, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(128, 128), (100, 246), (20, 22), (12, 30), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane481GenSource0089 :
    QuotientRankAtLeast (spanCodes [132, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(132, 148), (96, 104), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
