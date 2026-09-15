import QiushiPlane270GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit89From23
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane270GenSource0020 :
    QuotientRankAtLeast (spanCodes [320, 32, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(320, 8), (32, 128), (4, 2), (2, 4), (1, 3)]
    (codeMat 161) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane270GenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 32, 16, 8, 2, 1]) 3 := by
  apply quotientRankAtLeast_weaken (n := 3) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 64, 32, 16, 8, 4, 2, 1] [(256, 4), (128, 1), (64, 2), (32, 32), (16, 8), (8, 16), (2, 64), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_1

end QiushiMatmul
