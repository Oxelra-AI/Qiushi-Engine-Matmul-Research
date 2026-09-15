import QiushiPlane336GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit5FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane336GenSource0020 :
    QuotientRankAtLeast (spanCodes [256, 136, 72, 42, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (136, 264), (72, 8), (42, 509), (16, 360), (6, 3), (1, 1)]
    (codeMat 305) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane336GenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (130, 3), (68, 68), (38, 424), (16, 24), (14, 416), (1, 256)]
    (codeMat 85) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane336GenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 130, 70, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 130), (70, 245), (36, 8), (16, 128), (12, 264), (1, 360)]
    (codeMat 159) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane336GenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (128, 1), (66, 68), (32, 16), (16, 8), (12, 160), (1, 256)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane336GenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 130, 74, 40, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (130, 8), (74, 502), (40, 3), (16, 1), (6, 256), (1, 384)]
    (codeMat 106) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane336GenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 136, 64, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (136, 149), (64, 2), (34, 264), (16, 360), (6, 256), (1, 128)]
    (codeMat 92) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane336GenSource0026 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (130, 8), (66, 264), (32, 2), (16, 1), (12, 149), (1, 360)]
    (codeMat 298) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane336GenSource0027 :
    QuotientRankAtLeast (spanCodes [256, 136, 64, 34, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (136, 68), (64, 1), (34, 160), (16, 256), (4, 16), (1, 8)]
    (codeMat 140) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane336GenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 66, 32, 16, 8, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(256, 64), (66, 160), (32, 1), (16, 4), (8, 2), (4, 8), (1, 16)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

theorem plane336GenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 128, 96, 16, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(256, 16), (128, 8), (96, 160), (16, 64), (4, 2), (2, 1), (1, 4)]
    (codeMat 161) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

end QiushiMatmul
