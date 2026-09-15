import QiushiGlobalOrbitUnused92Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane92UnusedGenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 64, 16, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(160, 80), (64, 256), (16, 8), (4, 2), (2, 1), (1, 4)]
    (codeMat 273) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane92UnusedGenSource0001 :
    QuotientRankAtLeast (spanCodes [160, 72, 24, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(160, 344), (72, 256), (24, 8), (4, 6), (2, 5), (1, 4)]
    (codeMat 401) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane92UnusedGenSource0002 :
    QuotientRankAtLeast (spanCodes [128, 80, 32, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(128, 8), (80, 80), (32, 256), (4, 4), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane92UnusedGenSource0003 :
    QuotientRankAtLeast (spanCodes [136, 80, 40, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(136, 88), (80, 80), (40, 256), (4, 6), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane92UnusedGenSource0004 :
    QuotientRankAtLeast (spanCodes [272, 160, 80, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(272, 88), (160, 80), (80, 344), (4, 2), (2, 3), (1, 6)]
    (codeMat 305) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane92UnusedGenSource0005 :
    QuotientRankAtLeast (spanCodes [288, 160, 80, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(288, 256), (160, 264), (80, 336), (4, 4), (2, 5), (1, 7)]
    (codeMat 417) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane92UnusedGenSource0006 :
    QuotientRankAtLeast (spanCodes [256, 160, 80, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 8, 4, 2, 1] [(256, 256), (160, 160), (80, 80), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_9

theorem plane92UnusedGenSource0007 :
    QuotientRankAtLeast (spanCodes [304, 160, 80, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 8, 4, 2, 1] [(304, 344), (160, 240), (80, 416), (8, 256), (4, 3), (2, 6), (1, 4)]
    (codeMat 161) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_9

theorem plane92UnusedGenSource0008 :
    QuotientRankAtLeast (spanCodes [280, 144, 80, 48, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 8, 4, 2, 1] [(280, 88), (144, 504), (80, 496), (48, 256), (4, 3), (2, 7), (1, 6)]
    (codeMat 161) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_9

theorem plane92UnusedGenSource0009 :
    QuotientRankAtLeast (spanCodes [256, 152, 80, 56, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 8, 4, 2, 1] [(256, 256), (152, 424), (80, 240), (56, 8), (4, 4), (2, 6), (1, 3)]
    (codeMat 273) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_9

end QiushiMatmul
