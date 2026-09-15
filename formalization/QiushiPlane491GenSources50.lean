import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0500 :
    QuotientRankAtLeast (spanCodes [272, 145, 80, 48, 9, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 138), (145, 30), (80, 373), (48, 130), (9, 384), (4, 1), (2, 3)]
    (codeMat 241) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0501 :
    QuotientRankAtLeast (spanCodes [272, 146, 82, 48, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 327), (146, 511), (82, 255), (48, 2), (8, 3), (6, 16), (1, 24)]
    (codeMat 266) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0502 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 34, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 149), (128, 511), (80, 227), (34, 23), (10, 31), (4, 2), (1, 3)]
    (codeMat 465) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0503 :
    QuotientRankAtLeast (spanCodes [274, 144, 80, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(274, 138), (144, 3), (80, 508), (50, 136), (10, 480), (4, 128), (1, 256)]
    (codeMat 94) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0504 :
    QuotientRankAtLeast (spanCodes [258, 130, 80, 32, 8, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 176), (130, 432), (80, 70), (32, 2), (8, 1), (4, 16), (1, 8)]
    (codeMat 266) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0505 :
    QuotientRankAtLeast (spanCodes [274, 146, 80, 48, 8, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(274, 503), (146, 511), (80, 23), (48, 1), (8, 2), (4, 384), (1, 128)]
    (codeMat 98) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0506 :
    QuotientRankAtLeast (spanCodes [256, 140, 72, 44, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (140, 169), (72, 3), (44, 424), (28, 168), (2, 8), (1, 24)]
    (codeMat 142) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0507 :
    QuotientRankAtLeast (spanCodes [256, 130, 65, 33, 17, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(256, 9), (130, 5), (65, 2), (33, 80), (17, 336), (4, 8)]
    (codeMat 141) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane491GenSource0508 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 18, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (128, 3), (66, 28), (34, 88), (18, 216), (4, 8), (1, 32)]
    (codeMat 140) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0509 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (128, 2), (66, 20), (34, 208), (16, 128), (6, 8), (1, 32)]
    (codeMat 140) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
