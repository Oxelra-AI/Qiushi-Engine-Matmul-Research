import QiushiPlane255GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit11FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane255GenSource0020 :
    QuotientRankAtLeast (spanCodes [388, 68, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(388, 240), (68, 112), (36, 54), (20, 53), (8, 1), (2, 40), (1, 8)]
    (codeMat 266) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane255GenSource0021 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(260, 8), (132, 352), (64, 5), (32, 16), (8, 2), (2, 256), (1, 4)]
    (codeMat 85) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane255GenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 8), (132, 96), (64, 1), (32, 16), (8, 2), (2, 256), (1, 4)]
    (codeMat 84) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane255GenSource0023 :
    QuotientRankAtLeast (spanCodes [260, 148, 64, 32, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(260, 24), (148, 352), (64, 7), (32, 16), (8, 2), (2, 256), (1, 4)]
    (codeMat 87) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane255GenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 148, 64, 32, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 24), (148, 96), (64, 3), (32, 16), (8, 2), (2, 256), (1, 4)]
    (codeMat 86) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
