import QiushiPlane276GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit130From35T
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiWcOrbit146Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane276GenSource0010 :
    QuotientRankAtLeast (spanCodes [268, 96, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(268, 416), (96, 162), (28, 14), (2, 3), (1, 2)]
    (codeMat 465) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane276GenSource0011 :
    QuotientRankAtLeast (spanCodes [272, 76, 44, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 430), (76, 13), (44, 257), (2, 3), (1, 1)]
    (codeMat 241) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane276GenSource0012 :
    QuotientRankAtLeast (spanCodes [272, 156, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(272, 160), (156, 84), (96, 280), (2, 2), (1, 3)]
    (codeMat 161) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane276GenSource0013 :
    QuotientRankAtLeast (spanCodes [272, 172, 96, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(272, 440), (172, 335), (96, 280), (2, 1), (1, 3)]
    (codeMat 177) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

theorem plane276GenSource0014 :
    QuotientRankAtLeast (spanCodes [256, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (132, 160), (96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane276GenSource0015 :
    QuotientRankAtLeast (spanCodes [272, 144, 68, 36, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 326), (144, 3), (68, 178), (36, 432), (12, 176), (2, 24), (1, 16)]
    (codeMat 142) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane276GenSource0016 :
    QuotientRankAtLeast (spanCodes [264, 132, 64, 32, 24, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 96), (132, 28), (64, 8), (32, 256), (24, 128), (2, 3), (1, 1)]
    (codeMat 161) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane276GenSource0017 :
    QuotientRankAtLeast (spanCodes [272, 132, 68, 36, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 224), (132, 31), (68, 23), (36, 511), (12, 151), (2, 3), (1, 2)]
    (codeMat 417) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane276GenSource0018 :
    QuotientRankAtLeast (spanCodes [272, 144, 64, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 264), (144, 8), (64, 128), (32, 360), (12, 149), (2, 1), (1, 2)]
    (codeMat 305) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane276GenSource0019 :
    QuotientRankAtLeast (spanCodes [260, 132, 96, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (132, 151), (96, 224), (20, 23), (12, 31), (2, 2), (1, 3)]
    (codeMat 401) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
