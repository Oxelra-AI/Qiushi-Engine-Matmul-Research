import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0310 :
    QuotientRankAtLeast (spanCodes [257, 145, 65, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 89), (145, 30), (65, 219), (33, 88), (9, 216), (4, 8), (3, 40)]
    (codeMat 142) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0311 :
    QuotientRankAtLeast (spanCodes [258, 130, 69, 34, 18, 10]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 137), (130, 128), (69, 283), (34, 138), (18, 130), (10, 170)]
    (codeMat 342) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane489GenSource0312 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 488), (130, 360), (66, 232), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 270) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0313 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 235), (129, 381), (65, 511), (34, 232), (18, 360), (10, 488), (7, 8)]
    (codeMat 142) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0314 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 33, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 287), (129, 126), (66, 119), (33, 414), (18, 511), (10, 503), (7, 130)]
    (codeMat 407) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0315 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 35, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 488), (130, 128), (65, 256), (35, 503), (16, 130), (10, 276), (7, 8)]
    (codeMat 335) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0316 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 50, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(258, 10), (130, 3), (65, 5), (50, 88), (10, 344), (6, 8)]
    (codeMat 141) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane489GenSource0317 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 139), (131, 413), (67, 245), (34, 138), (19, 414), (10, 373), (6, 130)]
    (codeMat 478) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0318 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 510), (129, 363), (65, 3), (34, 503), (19, 235), (10, 373), (6, 511)]
    (codeMat 477) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0319 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 33, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 255), (129, 374), (66, 246), (33, 105), (19, 373), (10, 414), (6, 511)]
    (codeMat 351) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
