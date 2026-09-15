import QiushiGlobalOrbitUnused184Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit79Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane184UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [272, 146, 84, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 96, 20, 10, 1] [(272, 11), (146, 192), (84, 106), (32, 1), (10, 223), (1, 292)]
    (codeMat 482) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit82_lb14_unconditional

theorem plane184UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [278, 148, 84, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 96, 20, 10, 1] [(278, 497), (148, 202), (84, 494), (32, 325), (10, 347), (1, 192)]
    (codeMat 318) (codeMat 342) (codeMat 215) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit82_lb14_unconditional

theorem plane184UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [276, 150, 84, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 160, 96, 20, 10, 1] [(276, 11), (150, 21), (84, 445), (32, 1), (10, 96), (1, 360)]
    (codeMat 250) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit79_lb14_wc

theorem plane184UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [384, 80, 32, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(384, 256), (80, 112), (32, 16), (8, 8), (4, 2), (2, 6), (1, 1)]
    (codeMat 273) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
