import QiushiGlobalOrbitUnused383Data
import QiushiCertifiedTransport
import QiushiMonoOrbit38From11
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane383UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [288, 64, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 128, 20, 8, 2, 1] [(288, 8), (64, 128), (18, 438), (10, 150), (4, 1), (1, 2)]
    (codeMat 305) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit38_lb12_mono

theorem plane383UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [288, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 128, 20, 8, 2, 1] [(288, 8), (66, 151), (18, 438), (10, 150), (6, 130), (1, 2)]
    (codeMat 142) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit38_lb12_mono

theorem plane383UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [289, 161, 65, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 131), (161, 380), (65, 384), (17, 96), (8, 256), (5, 1), (2, 8)]
    (codeMat 185) (codeMat 340) (codeMat 85) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane383UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 37, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 350), (68, 332), (37, 264), (17, 160), (8, 256), (2, 432)]
    (codeMat 159) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane383UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 52), (129, 211), (64, 130), (16, 216), (9, 128), (4, 32), (3, 8)]
    (codeMat 207) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane383UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 65, 33, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 219), (65, 130), (33, 11), (16, 54), (9, 2), (5, 8), (3, 32)]
    (codeMat 395) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane383UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 33, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 130), (64, 9), (33, 28), (19, 287), (10, 252), (4, 3)]
    (codeMat 236) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane383UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 33, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 511), (66, 503), (33, 413), (19, 235), (10, 373), (6, 384)]
    (codeMat 500) (codeMat 247) (codeMat 379) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
