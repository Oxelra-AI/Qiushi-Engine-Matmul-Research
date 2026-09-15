import QiushiGlobalOrbitUnused308Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane308UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [288, 160, 96, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 511), (160, 509), (96, 381), (16, 360), (10, 96), (6, 1), (1, 8)]
    (codeMat 225) (codeMat 444) (codeMat 110) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane308UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [288, 162, 96, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 130), (162, 245), (96, 381), (16, 360), (10, 96), (6, 9), (1, 8)]
    (codeMat 241) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane308UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 511), (128, 128), (96, 381), (18, 256), (10, 104), (6, 9), (1, 8)]
    (codeMat 225) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane308UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [288, 130, 96, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 130), (130, 384), (96, 381), (18, 256), (10, 104), (6, 1), (1, 8)]
    (codeMat 241) (codeMat 396) (codeMat 106) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane308UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (132, 257), (68, 264), (36, 384), (20, 387), (10, 413), (1, 360)]
    (codeMat 372) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane308UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 381), (128, 130), (70, 509), (38, 373), (20, 235), (10, 413), (1, 360)]
    (codeMat 486) (codeMat 234) (codeMat 461) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane308UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 40), (128, 455), (68, 23), (36, 8), (20, 211), (8, 3), (2, 130), (1, 2)]
    (codeMat 395) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane308UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 40), (132, 464), (68, 23), (36, 8), (20, 208), (8, 3), (2, 128), (1, 2)]
    (codeMat 395) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
