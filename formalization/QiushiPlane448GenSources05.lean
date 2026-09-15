import QiushiPlane448GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane448GenSource0050 :
    QuotientRankAtLeast (spanCodes [276, 128, 64, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(276, 228), (128, 3), (64, 2), (32, 256), (12, 160), (2, 24), (1, 16)]
    (codeMat 140) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane448GenSource0051 :
    QuotientRankAtLeast (spanCodes [260, 128, 76, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (128, 130), (76, 502), (32, 8), (28, 96), (2, 128), (1, 384)]
    (codeMat 85) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane448GenSource0052 :
    QuotientRankAtLeast (spanCodes [266, 136, 74, 40, 24, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(266, 281), (136, 34), (74, 272), (40, 1), (24, 2), (1, 432)]
    (codeMat 498) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane448GenSource0053 :
    QuotientRankAtLeast (spanCodes [260, 144, 68, 48, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 511), (144, 3), (68, 186), (48, 256), (12, 184), (2, 24), (1, 16)]
    (codeMat 142) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane448GenSource0054 :
    QuotientRankAtLeast (spanCodes [258, 144, 66, 48, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 424), (144, 325), (66, 168), (48, 3), (8, 2), (6, 24), (1, 16)]
    (codeMat 266) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane448GenSource0055 :
    QuotientRankAtLeast (spanCodes [256, 144, 64, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (144, 325), (64, 2), (48, 256), (10, 168), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
