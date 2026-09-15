import QiushiPlane267GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit5FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane267GenSource0020 :
    QuotientRankAtLeast (spanCodes [264, 136, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 149), (136, 148), (64, 2), (32, 360), (20, 96), (2, 256), (1, 128)]
    (codeMat 92) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0021 :
    QuotientRankAtLeast (spanCodes [264, 140, 72, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 324), (140, 163), (72, 1), (32, 256), (28, 160), (2, 24), (1, 8)]
    (codeMat 142) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane267GenSource0022 :
    QuotientRankAtLeast (spanCodes [260, 136, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (136, 276), (64, 130), (32, 8), (20, 96), (2, 256), (1, 128)]
    (codeMat 85) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0023 :
    QuotientRankAtLeast (spanCodes [268, 128, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 228), (128, 2), (64, 3), (32, 256), (20, 160), (2, 16), (1, 24)]
    (codeMat 140) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane267GenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 144, 84, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (144, 130), (84, 372), (32, 8), (12, 96), (2, 128), (1, 256)]
    (codeMat 87) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0025 :
    QuotientRankAtLeast (spanCodes [268, 140, 72, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 484), (140, 161), (72, 3), (32, 256), (28, 160), (2, 8), (1, 24)]
    (codeMat 142) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane267GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 132, 72, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (132, 502), (72, 130), (32, 8), (28, 96), (2, 384), (1, 128)]
    (codeMat 87) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0027 :
    QuotientRankAtLeast (spanCodes [264, 128, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 68), (128, 2), (64, 1), (32, 256), (20, 160), (2, 16), (1, 8)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane267GenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 144, 84, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (144, 2), (84, 116), (32, 8), (12, 96), (2, 128), (1, 256)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 128, 80, 32, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(256, 8), (128, 16), (80, 160), (32, 64), (4, 1), (2, 2), (1, 4)]
    (codeMat 161) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

end QiushiMatmul
