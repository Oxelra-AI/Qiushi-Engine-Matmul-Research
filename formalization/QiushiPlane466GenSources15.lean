import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0150 :
    QuotientRankAtLeast (spanCodes [256, 144, 64, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (144, 325), (64, 2), (48, 256), (10, 168), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0151 :
    QuotientRankAtLeast (spanCodes [274, 128, 66, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(274, 238), (128, 325), (66, 170), (34, 424), (10, 168), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0152 :
    QuotientRankAtLeast (spanCodes [273, 129, 64, 32, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 277), (129, 104), (64, 8), (32, 130), (9, 1), (4, 128), (3, 256)]
    (codeMat 99) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0153 :
    QuotientRankAtLeast (spanCodes [272, 128, 64, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 20), (128, 2), (64, 1), (33, 96), (8, 8), (4, 256), (2, 128)]
    (codeMat 84) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0154 :
    QuotientRankAtLeast (spanCodes [257, 145, 64, 48, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 96), (145, 118), (64, 8), (48, 2), (8, 1), (4, 256), (2, 384)]
    (codeMat 98) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0155 :
    QuotientRankAtLeast (spanCodes [272, 128, 66, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 68), (128, 325), (66, 170), (32, 256), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0156 :
    QuotientRankAtLeast (spanCodes [256, 146, 64, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (146, 511), (64, 2), (48, 256), (10, 184), (4, 24), (1, 16)]
    (codeMat 140) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0157 :
    QuotientRankAtLeast (spanCodes [272, 132, 68, 32, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 224), (132, 28), (68, 20), (32, 256), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0158 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 36, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 373), (132, 406), (68, 414), (36, 384), (16, 2), (8, 3), (2, 130)]
    (codeMat 226) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0159 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (133, 68), (68, 326), (36, 24), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
