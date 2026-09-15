import QiushiPlane430GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit35FP
import QiushiStep99Orbit55Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane430GenSource0030 :
    QuotientRankAtLeast (spanCodes [172, 100, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(172, 140), (100, 175), (16, 3), (2, 1), (1, 9)]
    (codeMat 409) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane430GenSource0031 :
    QuotientRankAtLeast (spanCodes [290, 96, 16, 8, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 118), (96, 22), (16, 128), (8, 2), (4, 9), (1, 1)]
    (codeMat 273) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane430GenSource0032 :
    QuotientRankAtLeast (spanCodes [268, 134, 100, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(268, 42), (134, 164), (100, 367), (16, 32), (1, 448)]
    (codeMat 87) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane430GenSource0033 :
    QuotientRankAtLeast (spanCodes [288, 140, 100, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(288, 1), (140, 84), (100, 126), (16, 32), (1, 384)]
    (codeMat 86) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane430GenSource0034 :
    QuotientRankAtLeast (spanCodes [386, 74, 40, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(386, 96), (74, 118), (40, 130), (16, 128), (6, 8), (1, 9)]
    (codeMat 273) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane430GenSource0035 :
    QuotientRankAtLeast (spanCodes [134, 70, 34, 16, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(134, 168), (70, 133), (34, 304), (16, 32), (14, 132), (1, 2)]
    (codeMat 142) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane430GenSource0036 :
    QuotientRankAtLeast (spanCodes [290, 162, 96, 16, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(290, 132), (162, 164), (96, 138), (16, 438), (4, 2), (1, 3)]
    (codeMat 481) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane430GenSource0037 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (130, 2), (66, 52), (34, 80), (16, 128), (4, 8), (1, 32)]
    (codeMat 141) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane430GenSource0038 :
    QuotientRankAtLeast (spanCodes [264, 130, 74, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(264, 100), (130, 130), (74, 61), (42, 80), (16, 128), (4, 32), (1, 40)]
    (codeMat 143) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane430GenSource0039 :
    QuotientRankAtLeast (spanCodes [264, 136, 64, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 70), (136, 68), (64, 1), (34, 416), (16, 256), (6, 16), (1, 8)]
    (codeMat 140) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
