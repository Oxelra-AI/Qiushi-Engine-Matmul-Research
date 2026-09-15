import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0110 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 35, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 105), (129, 227), (64, 511), (35, 104), (17, 224), (10, 480), (4, 8)]
    (codeMat 206) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0111 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 96), (128, 256), (64, 384), (34, 105), (17, 276), (10, 406), (4, 8)]
    (codeMat 271) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0112 :
    QuotientRankAtLeast (spanCodes [256, 129, 67, 35, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (129, 373), (67, 414), (35, 10), (17, 29), (10, 30), (7, 8)]
    (codeMat 459) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0113 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 34, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 148), (128, 360), (67, 361), (34, 235), (17, 97), (10, 105), (7, 511)]
    (codeMat 477) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0114 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 35, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 29), (129, 20), (66, 22), (35, 381), (17, 276), (10, 406), (6, 8)]
    (codeMat 397) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0115 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 3), (66, 31), (34, 136), (17, 224), (10, 480), (6, 8)]
    (codeMat 204) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0116 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 34, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 284), (128, 8), (66, 105), (34, 129), (18, 1), (10, 257), (6, 130)]
    (codeMat 163) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0117 :
    QuotientRankAtLeast (spanCodes [260, 130, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (130, 2), (68, 324), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane461GenSource0118 :
    QuotientRankAtLeast (spanCodes [290, 162, 64, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 31), (162, 287), (64, 128), (18, 511), (10, 151), (4, 3), (1, 2)]
    (codeMat 305) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane461GenSource0119 :
    QuotientRankAtLeast (spanCodes [288, 162, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 256), (162, 287), (66, 23), (18, 511), (10, 151), (6, 3), (1, 2)]
    (codeMat 417) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
