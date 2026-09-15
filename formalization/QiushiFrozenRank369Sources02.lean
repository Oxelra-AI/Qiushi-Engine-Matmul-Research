import QiushiFrozenRank369Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane369RankCoverGenSource0020 :
    QuotientRankAtLeast (spanCodes [288, 160, 100, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 256), (160, 255), (100, 105), (20, 31), (8, 9), (2, 3), (1, 1)]
    (codeMat 409) (codeMat 275) (codeMat 275) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane369RankCoverGenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 2), (128, 1), (68, 20), (32, 128), (20, 82), (2, 9), (1, 54)]
    (codeMat 172) (codeMat 106) (codeMat 396) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit11_lb12

theorem plane369RankCoverGenSource0022 :
    QuotientRankAtLeast (spanCodes [268, 132, 72, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 418), (132, 77), (72, 16), (36, 256), (20, 69), (2, 1), (1, 2)]
    (codeMat 241) (codeMat 266) (codeMat 266) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane369RankCoverGenSource0023 :
    QuotientRankAtLeast (spanCodes [268, 140, 72, 44, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(268, 387), (140, 124), (72, 2), (44, 257), (20, 105), (2, 8), (1, 1)]
    (codeMat 241) (codeMat 277) (codeMat 277) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane369RankCoverGenSource0024 :
    QuotientRankAtLeast (spanCodes [266, 138, 72, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 84), (138, 484), (72, 24), (42, 68), (16, 256), (4, 2), (1, 3)]
    (codeMat 177) (codeMat 169) (codeMat 225) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane369RankCoverGenSource0025 :
    QuotientRankAtLeast (spanCodes [290, 160, 98, 18, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 353), (160, 287), (98, 158), (18, 130), (8, 3), (6, 9), (1, 1)]
    (codeMat 409) (codeMat 419) (codeMat 183) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane369RankCoverGenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 502), (160, 237), (66, 70), (18, 256), (10, 69), (6, 9), (1, 1)]
    (codeMat 249) (codeMat 421) (codeMat 179) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit10_lb12

theorem plane369RankCoverGenSource0027 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 32, 18, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(256, 5), (128, 4), (64, 3), (32, 360), (18, 256), (6, 8), (1, 24)]
    (codeMat 204) (codeMat 397) (codeMat 250) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.flatSeed_7

theorem plane369RankCoverGenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 136, 64, 40, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (136, 148), (64, 2), (40, 256), (18, 360), (6, 9), (1, 1)]
    (codeMat 161) (codeMat 405) (codeMat 407) true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

theorem plane369RankCoverGenSource0029 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 34, 20, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide +kernel)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (130, 256), (66, 104), (34, 22), (20, 20), (8, 9), (1, 8)]
    (codeMat 331) (codeMat 417) (codeMat 177) false
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
