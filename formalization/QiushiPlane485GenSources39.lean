import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0390 :
    QuotientRankAtLeast (spanCodes [262, 130, 66, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 480), (130, 256), (66, 104), (32, 511), (20, 284), (10, 105), (1, 8)]
    (codeMat 334) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0391 :
    QuotientRankAtLeast (spanCodes [290, 160, 98, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 387), (160, 373), (98, 124), (18, 360), (10, 352), (6, 384), (1, 256)]
    (codeMat 87) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0392 :
    QuotientRankAtLeast (spanCodes [256, 162, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (162, 246), (66, 178), (18, 432), (10, 176), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0393 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 503), (160, 70), (66, 178), (18, 432), (10, 176), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0394 :
    QuotientRankAtLeast (spanCodes [386, 64, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(386, 71), (64, 128), (34, 55), (18, 63), (10, 23), (6, 1), (1, 2)]
    (codeMat 273) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0395 :
    QuotientRankAtLeast (spanCodes [448, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(448, 4), (32, 8), (18, 216), (10, 209), (6, 128), (1, 130)]
    (codeMat 266) (codeMat 241) (codeMat 489) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane485GenSource0396 :
    QuotientRankAtLeast (spanCodes [256, 162, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (162, 228), (64, 2), (16, 256), (10, 160), (4, 24), (1, 16)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0397 :
    QuotientRankAtLeast (spanCodes [288, 128, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(288, 32), (128, 216), (68, 148), (20, 196), (8, 128), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0398 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (132, 454), (68, 452), (36, 504), (20, 496), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0399 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 197), (128, 3), (64, 2), (32, 40), (18, 216), (10, 208), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
