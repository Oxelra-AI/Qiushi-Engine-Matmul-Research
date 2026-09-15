import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 144, 64, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (144, 325), (64, 2), (48, 256), (10, 168), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane486GenSource0201 :
    QuotientRankAtLeast (spanCodes [273, 128, 64, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 158), (128, 3), (64, 1), (48, 360), (9, 8), (4, 384), (3, 128)]
    (codeMat 92) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane486GenSource0202 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 219), (132, 210), (68, 228), (36, 216), (20, 208), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane486GenSource0203 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (132, 198), (68, 196), (32, 216), (21, 112), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane486GenSource0204 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (129, 191), (68, 237), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane486GenSource0205 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (129, 191), (68, 109), (36, 32), (20, 248), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane486GenSource0206 :
    QuotientRankAtLeast (spanCodes [257, 133, 68, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (133, 210), (68, 109), (32, 32), (21, 80), (8, 40), (2, 128)]
    (codeMat 87) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane486GenSource0207 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (133, 82), (68, 237), (37, 240), (21, 208), (8, 40), (2, 128)]
    (codeMat 87) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane486GenSource0208 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 210), (130, 219), (64, 54), (34, 208), (18, 216), (10, 240), (4, 128)]
    (codeMat 86) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane486GenSource0209 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 112), (128, 216), (65, 32), (34, 198), (16, 3), (10, 196), (5, 128)]
    (codeMat 106) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
