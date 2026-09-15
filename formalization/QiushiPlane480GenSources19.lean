import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiMonoOrbit89From23
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0190 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (130, 2), (70, 324), (32, 24), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0191 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 3), (134, 196), (64, 130), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane480GenSource0192 :
    QuotientRankAtLeast (spanCodes [292, 128, 76, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(292, 216), (128, 5), (76, 208), (16, 4), (2, 2), (1, 128)]
    (codeMat 142) (codeMat 354) (codeMat 142) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0193 :
    QuotientRankAtLeast (spanCodes [260, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (132, 176), (96, 70), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0194 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (128, 2), (70, 68), (32, 24), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0195 :
    QuotientRankAtLeast (spanCodes [256, 130, 106, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 9), (130, 2), (106, 313), (16, 130), (4, 8), (1, 40)]
    (codeMat 461) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0196 :
    QuotientRankAtLeast (spanCodes [256, 128, 106, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 3), (128, 2), (106, 403), (16, 130), (6, 8), (1, 40)]
    (codeMat 396) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0197 :
    QuotientRankAtLeast (spanCodes [258, 130, 106, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 11), (130, 2), (106, 443), (16, 130), (6, 8), (1, 40)]
    (codeMat 461) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0198 :
    QuotientRankAtLeast (spanCodes [258, 128, 74, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 211), (128, 130), (74, 20), (34, 208), (16, 128), (6, 8), (1, 32)]
    (codeMat 142) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane480GenSource0199 :
    QuotientRankAtLeast (spanCodes [292, 130, 72, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(292, 4), (130, 9), (72, 130), (16, 8), (1, 128)]
    (codeMat 87) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

end QiushiMatmul
