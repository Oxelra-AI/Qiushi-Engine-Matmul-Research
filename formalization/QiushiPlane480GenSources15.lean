import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiMonoOrbit89From23
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0150 :
    QuotientRankAtLeast (spanCodes [384, 32, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(384, 4), (32, 8), (16, 9), (6, 2), (1, 128)]
    (codeMat 266) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane480GenSource0151 :
    QuotientRankAtLeast (spanCodes [256, 160, 16, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 8), (160, 80), (16, 128), (4, 1), (2, 2), (1, 4)]
    (codeMat 161) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0152 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(256, 4), (128, 1), (64, 2), (16, 8), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane480GenSource0153 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(260, 216), (128, 1), (68, 208), (16, 4), (2, 2), (1, 128)]
    (codeMat 140) (codeMat 354) (codeMat 142) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0154 :
    QuotientRankAtLeast (spanCodes [290, 128, 98, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(290, 272), (128, 2), (98, 273), (16, 130), (4, 32), (1, 40)]
    (codeMat 396) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0155 :
    QuotientRankAtLeast (spanCodes [288, 130, 98, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(288, 9), (130, 128), (98, 313), (16, 130), (4, 8), (1, 40)]
    (codeMat 335) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0156 :
    QuotientRankAtLeast (spanCodes [288, 128, 98, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(288, 3), (128, 128), (98, 403), (16, 130), (6, 8), (1, 40)]
    (codeMat 270) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0157 :
    QuotientRankAtLeast (spanCodes [290, 130, 98, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(290, 11), (130, 128), (98, 443), (16, 130), (6, 8), (1, 40)]
    (codeMat 335) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0158 :
    QuotientRankAtLeast (spanCodes [260, 130, 64, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(260, 4), (130, 1), (64, 130), (16, 8), (1, 128)]
    (codeMat 85) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane480GenSource0159 :
    QuotientRankAtLeast (spanCodes [288, 130, 98, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(288, 432), (130, 2), (98, 443), (16, 130), (6, 32), (1, 40)]
    (codeMat 461) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

end QiushiMatmul
