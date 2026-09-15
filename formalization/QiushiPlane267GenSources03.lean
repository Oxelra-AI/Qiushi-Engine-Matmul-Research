import QiushiPlane267GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit5FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane267GenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 136, 80, 32, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(256, 72), (136, 160), (80, 176), (32, 64), (4, 1), (2, 4), (1, 6)]
    (codeMat 177) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

theorem plane267GenSource0031 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 32, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(272, 96), (128, 8), (80, 112), (32, 256), (4, 4), (2, 1), (1, 6)]
    (codeMat 161) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

theorem plane267GenSource0032 :
    QuotientRankAtLeast (spanCodes [280, 136, 80, 32, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(280, 352), (136, 112), (80, 120), (32, 256), (4, 4), (2, 6), (1, 7)]
    (codeMat 177) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
