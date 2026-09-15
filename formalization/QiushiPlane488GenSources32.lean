import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0320 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (130, 3), (66, 387), (34, 227), (19, 414), (10, 235), (7, 130)]
    (codeMat 277) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0321 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (130, 216), (66, 240), (34, 196), (16, 3), (10, 198), (5, 128)]
    (codeMat 98) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0322 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 509), (130, 3), (64, 360), (32, 130), (19, 373), (10, 414), (5, 511)]
    (codeMat 477) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0323 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 257), (131, 326), (64, 325), (32, 8), (18, 432), (10, 424), (5, 256)]
    (codeMat 85) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0324 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 32, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 208), (131, 240), (64, 40), (32, 130), (17, 198), (10, 197), (4, 128)]
    (codeMat 99) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0325 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 324), (130, 1), (67, 71), (35, 160), (18, 8), (10, 440), (4, 256)]
    (codeMat 93) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0326 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 32, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 91), (128, 54), (64, 63), (32, 216), (17, 112), (10, 120), (7, 128)]
    (codeMat 95) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0327 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 35, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 88), (131, 112), (67, 120), (35, 131), (17, 70), (10, 71), (7, 128)]
    (codeMat 99) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0328 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 240), (130, 216), (66, 248), (34, 198), (16, 3), (10, 199), (7, 128)]
    (codeMat 98) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0329 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 35, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (131, 196), (67, 199), (35, 136), (18, 32), (10, 248), (7, 128)]
    (codeMat 92) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
