import QiushiPlane269GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiWcOrbit25Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane269GenSource0020 :
    QuotientRankAtLeast (spanCodes [264, 140, 72, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 324), (140, 163), (72, 1), (32, 256), (28, 160), (2, 24), (1, 8)]
    (codeMat 142) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane269GenSource0021 :
    QuotientRankAtLeast (spanCodes [264, 132, 72, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 324), (132, 162), (72, 1), (32, 256), (20, 160), (2, 16), (1, 8)]
    (codeMat 142) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane269GenSource0022 :
    QuotientRankAtLeast (spanCodes [260, 132, 80, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (132, 502), (80, 276), (32, 8), (12, 96), (2, 384), (1, 256)]
    (codeMat 87) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane269GenSource0023 :
    QuotientRankAtLeast (spanCodes [264, 128, 64, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 68), (128, 3), (64, 1), (32, 256), (28, 160), (2, 24), (1, 8)]
    (codeMat 140) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane269GenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 148, 68, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 130), (148, 52), (68, 89), (32, 128), (12, 80), (2, 32), (1, 8)]
    (codeMat 143) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane269GenSource0025 :
    QuotientRankAtLeast (spanCodes [264, 152, 32, 4, 2, 1]) 11 := by
  apply quotientRankAtLeast_weaken (n := 11) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 8, 4, 2, 1] [(264, 88), (152, 336), (32, 8), (4, 1), (2, 5), (1, 2)]
    (codeMat 401) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit25_lb11_wc

theorem plane269GenSource0026 :
    QuotientRankAtLeast (spanCodes [264, 200, 32, 4, 2, 1]) 11 := by
  apply quotientRankAtLeast_weaken (n := 11) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 8, 4, 2, 1] [(264, 88), (200, 344), (32, 8), (4, 1), (2, 6), (1, 3)]
    (codeMat 273) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit25_lb11_wc

theorem plane269GenSource0027 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane269GenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (132, 70), (68, 68), (32, 8), (20, 112), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane269GenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 128, 80, 32, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 8), (128, 16), (80, 160), (32, 64), (8, 256), (4, 1), (2, 2), (1, 4)]
    (codeMat 161) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
