import QiushiPlane469GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane469GenSource0170 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 151), (128, 2), (64, 3), (33, 224), (18, 128), (10, 136), (6, 360)]
    (codeMat 212) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0171 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (132, 21), (64, 9), (36, 511), (20, 381), (10, 105), (1, 8)]
    (codeMat 461) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0172 :
    QuotientRankAtLeast (spanCodes [258, 128, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 276), (128, 130), (70, 227), (38, 148), (18, 2), (10, 362), (1, 511)]
    (codeMat 491) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0173 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 71), (132, 70), (70, 324), (34, 440), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane469GenSource0174 :
    QuotientRankAtLeast (spanCodes [258, 162, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 487), (162, 228), (66, 162), (16, 256), (10, 160), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane469GenSource0175 :
    QuotientRankAtLeast (spanCodes [258, 160, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 257), (160, 97), (64, 130), (18, 360), (10, 151), (6, 1), (1, 2)]
    (codeMat 369) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0176 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 510), (129, 363), (65, 3), (34, 503), (19, 235), (10, 373), (6, 511)]
    (codeMat 477) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0177 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 278), (128, 130), (67, 139), (33, 232), (18, 128), (10, 136), (5, 360)]
    (codeMat 215) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0178 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (129, 232), (65, 384), (34, 31), (16, 3), (10, 30), (5, 8)]
    (codeMat 330) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane469GenSource0179 :
    QuotientRankAtLeast (spanCodes [256, 132, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (132, 68), (65, 3), (37, 424), (21, 416), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
