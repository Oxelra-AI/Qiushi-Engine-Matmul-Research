import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0140 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (134, 353), (66, 404), (34, 105), (20, 97), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0141 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (130, 256), (66, 104), (34, 406), (20, 276), (10, 105), (1, 8)]
    (codeMat 334) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0142 :
    QuotientRankAtLeast (spanCodes [386, 64, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(386, 199), (64, 128), (32, 32), (18, 63), (10, 23), (6, 3), (1, 2)]
    (codeMat 273) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane454GenSource0143 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (128, 3), (65, 325), (33, 184), (18, 24), (10, 424), (6, 256)]
    (codeMat 92) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane454GenSource0144 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 2), (128, 1), (66, 70), (34, 80), (16, 8), (10, 112), (4, 128)]
    (codeMat 84) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane454GenSource0145 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 105), (129, 227), (64, 511), (32, 1), (16, 3), (10, 31), (4, 8)]
    (codeMat 458) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0146 :
    QuotientRankAtLeast (spanCodes [257, 130, 65, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 104), (130, 128), (65, 256), (33, 97), (16, 130), (10, 276), (4, 8)]
    (codeMat 335) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0147 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 21), (131, 22), (67, 20), (35, 381), (17, 406), (10, 276), (5, 8)]
    (codeMat 460) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0148 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 10), (131, 31), (65, 3), (33, 136), (17, 480), (10, 224), (5, 8)]
    (codeMat 205) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0149 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 20), (128, 9), (65, 2), (33, 276), (20, 97), (8, 130), (2, 8)]
    (codeMat 461) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
