import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0310 :
    QuotientRankAtLeast (spanCodes [256, 194, 34, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (194, 240), (34, 34), (16, 54), (10, 29), (6, 32), (1, 40)]
    (codeMat 267) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0311 :
    QuotientRankAtLeast (spanCodes [272, 144, 80, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 510), (144, 511), (80, 508), (50, 392), (10, 224), (4, 384), (1, 256)]
    (codeMat 92) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0312 :
    QuotientRankAtLeast (spanCodes [272, 144, 82, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 10), (144, 3), (82, 252), (48, 8), (10, 224), (4, 128), (1, 256)]
    (codeMat 86) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0313 :
    QuotientRankAtLeast (spanCodes [272, 128, 66, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 257), (128, 325), (66, 170), (48, 256), (10, 168), (4, 8), (1, 16)]
    (codeMat 142) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane426GenSource0314 :
    QuotientRankAtLeast (spanCodes [272, 146, 66, 34, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 235), (146, 384), (66, 148), (34, 30), (10, 22), (4, 3), (1, 2)]
    (codeMat 465) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0315 :
    QuotientRankAtLeast (spanCodes [256, 130, 96, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (130, 1), (96, 276), (16, 8), (10, 96), (4, 128), (1, 256)]
    (codeMat 85) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0316 :
    QuotientRankAtLeast (spanCodes [256, 162, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (162, 228), (64, 2), (16, 256), (10, 160), (4, 24), (1, 16)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane426GenSource0317 :
    QuotientRankAtLeast (spanCodes [272, 148, 80, 48, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 510), (148, 118), (80, 150), (48, 1), (8, 2), (2, 384), (1, 128)]
    (codeMat 106) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0318 :
    QuotientRankAtLeast (spanCodes [260, 132, 100, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (132, 151), (100, 119), (20, 23), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0319 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
