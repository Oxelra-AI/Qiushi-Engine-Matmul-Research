import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0370 :
    QuotientRankAtLeast (spanCodes [257, 145, 65, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 89), (145, 30), (65, 219), (33, 88), (9, 216), (4, 8), (3, 40)]
    (codeMat 142) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0371 :
    QuotientRankAtLeast (spanCodes [384, 65, 33, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(384, 128), (65, 216), (33, 60), (16, 54), (9, 3), (4, 32), (3, 40)]
    (codeMat 267) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0372 :
    QuotientRankAtLeast (spanCodes [257, 128, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 503), (128, 325), (81, 246), (49, 176), (9, 432), (5, 8), (3, 24)]
    (codeMat 142) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0373 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 264), (130, 384), (66, 232), (34, 276), (19, 414), (10, 235), (7, 8)]
    (codeMat 334) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0374 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 35, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 258), (130, 1), (67, 71), (35, 272), (18, 8), (10, 440), (7, 256)]
    (codeMat 93) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0375 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 34, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 70), (130, 2), (66, 327), (34, 176), (16, 16), (10, 184), (6, 256)]
    (codeMat 85) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0376 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 228), (130, 219), (64, 54), (32, 32), (18, 216), (10, 240), (5, 128)]
    (codeMat 86) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0377 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 392), (129, 224), (66, 480), (34, 30), (16, 3), (10, 31), (5, 8)]
    (codeMat 330) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0378 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 362), (131, 508), (64, 511), (32, 128), (16, 256), (10, 224), (5, 360)]
    (codeMat 157) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0379 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 68), (130, 2), (66, 327), (34, 160), (16, 16), (10, 184), (4, 256)]
    (codeMat 85) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
