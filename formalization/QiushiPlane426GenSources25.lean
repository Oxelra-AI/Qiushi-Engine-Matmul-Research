import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0250 :
    QuotientRankAtLeast (spanCodes [260, 132, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (132, 353), (66, 278), (34, 105), (20, 97), (10, 406), (1, 130)]
    (codeMat 415) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0251 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 23), (134, 21), (64, 1), (32, 511), (22, 381), (10, 97), (1, 8)]
    (codeMat 460) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0252 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 34, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 413), (134, 245), (66, 278), (34, 414), (22, 373), (10, 406), (1, 130)]
    (codeMat 407) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0253 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 71), (132, 70), (70, 324), (34, 440), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane426GenSource0254 :
    QuotientRankAtLeast (spanCodes [258, 128, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 276), (128, 130), (70, 227), (38, 148), (18, 2), (10, 362), (1, 511)]
    (codeMat 491) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0255 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 36, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 136), (130, 128), (70, 96), (36, 3), (18, 2), (10, 509), (1, 360)]
    (codeMat 355) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0256 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (134, 508), (70, 509), (34, 480), (16, 256), (10, 96), (1, 360)]
    (codeMat 156) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0257 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (132, 29), (64, 1), (38, 232), (16, 360), (10, 96), (1, 8)]
    (codeMat 204) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0258 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 34, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 30), (134, 29), (64, 1), (34, 414), (22, 373), (10, 97), (1, 8)]
    (codeMat 460) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0259 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 34, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 363), (128, 3), (70, 362), (34, 235), (22, 373), (10, 227), (1, 511)]
    (codeMat 468) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
