import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0310 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (129, 191), (68, 109), (36, 32), (20, 248), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0311 :
    QuotientRankAtLeast (spanCodes [260, 129, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (129, 96), (64, 8), (32, 2), (20, 149), (8, 1), (2, 360)]
    (codeMat 354) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0312 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (133, 149), (68, 510), (36, 8), (20, 264), (8, 384), (2, 360)]
    (codeMat 157) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0313 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 2), (128, 3), (66, 198), (34, 208), (18, 216), (10, 240), (4, 128)]
    (codeMat 84) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0314 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 34, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 149), (130, 3), (66, 363), (34, 227), (19, 373), (10, 235), (4, 511)]
    (codeMat 405) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0315 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 362), (130, 1), (64, 511), (32, 128), (18, 8), (10, 392), (5, 360)]
    (codeMat 157) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0316 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 8), (130, 216), (64, 32), (32, 1), (16, 3), (10, 196), (6, 128)]
    (codeMat 98) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0317 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (128, 3), (65, 325), (33, 184), (18, 24), (10, 424), (6, 256)]
    (codeMat 92) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0318 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 259), (130, 3), (64, 384), (32, 511), (19, 414), (10, 373), (7, 130)]
    (codeMat 285) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0319 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 131), (131, 387), (64, 384), (32, 8), (19, 235), (10, 373), (7, 130)]
    (codeMat 277) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
