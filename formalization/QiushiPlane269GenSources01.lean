import QiushiPlane269GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit23FP
import QiushiWcOrbit114Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane269GenSource0010 :
    QuotientRankAtLeast (spanCodes [264, 144, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(264, 416), (144, 8), (32, 256), (2, 1), (1, 2)]
    (codeMat 177) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane269GenSource0011 :
    QuotientRankAtLeast (spanCodes [264, 192, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(264, 160), (192, 8), (32, 256), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane269GenSource0012 :
    QuotientRankAtLeast (spanCodes [264, 64, 32, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(264, 80), (64, 8), (32, 128), (4, 2), (2, 4), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane269GenSource0013 :
    QuotientRankAtLeast (spanCodes [264, 72, 32, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(264, 208), (72, 216), (32, 128), (4, 2), (2, 4), (1, 3)]
    (codeMat 161) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane269GenSource0014 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 2), (132, 52), (64, 9), (32, 128), (12, 80), (2, 32), (1, 8)]
    (codeMat 141) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane269GenSource0015 :
    QuotientRankAtLeast (spanCodes [260, 148, 84, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (148, 502), (84, 372), (32, 8), (12, 96), (2, 384), (1, 256)]
    (codeMat 85) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane269GenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 148, 80, 32, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (148, 118), (80, 22), (32, 1), (8, 2), (2, 384), (1, 128)]
    (codeMat 98) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane269GenSource0017 :
    QuotientRankAtLeast (spanCodes [264, 128, 76, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 245), (128, 130), (76, 374), (32, 360), (28, 96), (2, 128), (1, 384)]
    (codeMat 93) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane269GenSource0018 :
    QuotientRankAtLeast (spanCodes [264, 140, 68, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 413), (140, 226), (68, 374), (32, 360), (28, 96), (2, 128), (1, 384)]
    (codeMat 95) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane269GenSource0019 :
    QuotientRankAtLeast (spanCodes [264, 136, 64, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 149), (136, 150), (64, 2), (32, 360), (28, 96), (2, 384), (1, 128)]
    (codeMat 92) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
