import QiushiPlane471LowerGenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit137From55
import QiushiStep99Mono3032
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471LowerGenSource0050 :
    QuotientRankAtLeast (spanCodes [289, 64, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 80, 32, 2, 1] [(289, 321), (64, 3), (20, 306), (9, 2), (3, 32)]
    (codeMat 95) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit137_lb14_mono

theorem plane471LowerGenSource0051 :
    QuotientRankAtLeast (spanCodes [288, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(288, 256), (68, 76), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane471LowerGenSource0052 :
    QuotientRankAtLeast (spanCodes [289, 65, 16, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 32, 8, 2, 1] [(289, 131), (65, 9), (16, 32), (8, 8), (5, 128), (2, 256)]
    (codeMat 87) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_42

end QiushiMatmul
