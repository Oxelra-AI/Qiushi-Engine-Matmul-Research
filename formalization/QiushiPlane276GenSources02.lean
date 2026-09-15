import QiushiPlane276GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit43From14
import QiushiWcOrbit25Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane276GenSource0020 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 32), (160, 272), (96, 280), (16, 128), (2, 2), (1, 3)]
    (codeMat 161) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane276GenSource0021 :
    QuotientRankAtLeast (spanCodes [272, 144, 64, 32, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(272, 160), (144, 128), (64, 8), (32, 432), (2, 2), (1, 1)]
    (codeMat 417) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane276GenSource0022 :
    QuotientRankAtLeast (spanCodes [272, 136, 72, 40, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(272, 280), (136, 136), (72, 8), (40, 432), (2, 3), (1, 1)]
    (codeMat 305) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane276GenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 72, 40, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 432), (72, 128), (40, 32), (16, 8), (2, 1), (1, 2)]
    (codeMat 401) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane276GenSource0024 :
    QuotientRankAtLeast (spanCodes [264, 136, 96, 24, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(264, 312), (136, 136), (96, 280), (24, 128), (2, 1), (1, 3)]
    (codeMat 177) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane276GenSource0025 :
    QuotientRankAtLeast (spanCodes [272, 64, 32, 4, 2, 1]) 11 := by
  apply quotientRankAtLeast_weaken (n := 11) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 8, 4, 2, 1] [(272, 80), (64, 256), (32, 8), (4, 1), (2, 2), (1, 4)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit25_lb11_wc

theorem plane276GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (132, 326), (64, 2), (32, 40), (20, 368), (12, 336), (2, 384), (1, 128)]
    (codeMat 84) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane276GenSource0027 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (128, 2), (68, 454), (36, 504), (20, 464), (12, 496), (2, 128), (1, 384)]
    (codeMat 84) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane276GenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 196), (68, 198), (36, 216), (16, 32), (12, 240), (2, 256), (1, 384)]
    (codeMat 84) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane276GenSource0029 :
    QuotientRankAtLeast (spanCodes [272, 136, 80, 48, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(272, 272), (136, 112), (80, 120), (48, 256), (4, 2), (2, 6), (1, 7)]
    (codeMat 177) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
