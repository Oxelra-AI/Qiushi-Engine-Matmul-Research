import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiPlane470LowerGenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0230 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 20, 8, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 18), (132, 164), (64, 9), (32, 16), (20, 160), (8, 8), (2, 256), (1, 64)]
    (codeMat 86) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane470GenSource0231 :
    QuotientRankAtLeast (spanCodes [259, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(259, 259), (84, 84), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470LowerGen_lb17

end QiushiMatmul
