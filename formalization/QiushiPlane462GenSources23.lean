import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0230 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 196), (130, 1), (67, 71), (32, 32), (16, 8), (10, 120), (7, 128)]
    (codeMat 85) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0231 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 210), (130, 219), (64, 54), (34, 208), (18, 216), (10, 240), (4, 128)]
    (codeMat 86) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0232 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 210), (131, 228), (64, 63), (35, 80), (18, 32), (10, 248), (4, 128)]
    (codeMat 95) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0233 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (130, 216), (64, 32), (32, 2), (16, 3), (10, 196), (4, 128)]
    (codeMat 98) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0234 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 32, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 208), (131, 240), (64, 40), (32, 130), (17, 198), (10, 197), (4, 128)]
    (codeMat 99) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0235 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (129, 510), (65, 511), (33, 488), (18, 384), (10, 392), (5, 360)]
    (codeMat 212) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0236 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 32, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 228), (130, 9), (65, 54), (32, 32), (16, 8), (10, 112), (5, 128)]
    (codeMat 87) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0237 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 136), (130, 256), (65, 384), (33, 363), (17, 148), (10, 150), (5, 360)]
    (codeMat 355) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0238 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (132, 82), (68, 100), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0239 :
    QuotientRankAtLeast (spanCodes [257, 133, 68, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (133, 210), (68, 109), (32, 32), (21, 80), (8, 40), (2, 128)]
    (codeMat 87) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
