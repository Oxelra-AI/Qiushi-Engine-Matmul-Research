import QiushiGlobalOrbitUnused398Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane398UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 343), (128, 9), (65, 325), (33, 168), (18, 8), (10, 264), (6, 432)]
    (codeMat 159) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane398UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 70), (128, 384), (64, 128), (32, 9), (16, 54), (10, 20), (4, 1), (1, 2)]
    (codeMat 281) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane398UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 216), (130, 63), (66, 60), (34, 404), (16, 54), (10, 20), (4, 288), (1, 32)]
    (codeMat 95) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane398UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 504), (130, 438), (66, 150), (34, 62), (18, 54), (10, 22), (6, 1), (1, 2)]
    (codeMat 401) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane398UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 325), (128, 40), (65, 9), (33, 418), (17, 20), (8, 54), (5, 288), (2, 32)]
    (codeMat 93) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
