import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0340 :
    QuotientRankAtLeast (spanCodes [263, 135, 68, 36, 18, 10]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(263, 402), (135, 411), (68, 283), (36, 32), (18, 40), (10, 170)]
    (codeMat 351) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane488GenSource0341 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (130, 219), (64, 54), (32, 8), (18, 216), (10, 240), (6, 128)]
    (codeMat 86) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0342 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 182), (129, 228), (65, 63), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 94) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0343 :
    QuotientRankAtLeast (spanCodes [257, 128, 66, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 483), (128, 9), (66, 119), (34, 136), (18, 8), (10, 392), (7, 360)]
    (codeMat 159) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0344 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (129, 70), (66, 71), (34, 424), (18, 432), (10, 440), (7, 256)]
    (codeMat 85) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0345 :
    QuotientRankAtLeast (spanCodes [257, 129, 67, 35, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 284), (129, 414), (67, 235), (35, 264), (18, 384), (10, 232), (7, 8)]
    (codeMat 207) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0346 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 360), (64, 3), (32, 8), (19, 414), (10, 373), (7, 511)]
    (codeMat 468) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0347 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 259), (130, 2), (64, 325), (32, 24), (16, 16), (10, 168), (7, 256)]
    (codeMat 85) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0348 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 29), (129, 31), (64, 3), (32, 360), (17, 480), (10, 224), (7, 8)]
    (codeMat 204) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0349 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 324), (129, 70), (66, 71), (34, 416), (18, 432), (10, 440), (4, 256)]
    (codeMat 85) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
