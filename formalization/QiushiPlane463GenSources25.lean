import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0250 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 104), (131, 232), (64, 384), (32, 1), (16, 3), (10, 30), (4, 8)]
    (codeMat 266) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0251 :
    QuotientRankAtLeast (spanCodes [257, 133, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 119), (133, 139), (68, 126), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 215) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0252 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 22), (68, 23), (32, 130), (20, 406), (9, 511), (3, 8)]
    (codeMat 396) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0253 :
    QuotientRankAtLeast (spanCodes [257, 133, 68, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 227), (133, 381), (68, 284), (37, 224), (16, 360), (9, 256), (3, 8)]
    (codeMat 207) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0254 :
    QuotientRankAtLeast (spanCodes [272, 145, 65, 33, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 287), (145, 127), (65, 8), (33, 131), (9, 1), (5, 128), (3, 384)]
    (codeMat 107) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0255 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 149), (68, 150), (32, 128), (21, 96), (8, 384), (2, 360)]
    (codeMat 156) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0256 :
    QuotientRankAtLeast (spanCodes [257, 133, 68, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 148), (133, 509), (68, 150), (32, 256), (20, 96), (8, 384), (2, 360)]
    (codeMat 157) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0257 :
    QuotientRankAtLeast (spanCodes [257, 133, 68, 37, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 71), (133, 324), (68, 70), (37, 440), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0258 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 68), (68, 70), (36, 8), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0259 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (128, 2), (68, 324), (34, 168), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
