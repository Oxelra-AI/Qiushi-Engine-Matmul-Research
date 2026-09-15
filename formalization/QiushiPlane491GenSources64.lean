import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0640 :
    QuotientRankAtLeast (spanCodes [257, 128, 72, 32, 24, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 168), (128, 256), (72, 325), (32, 2), (24, 1), (4, 16), (3, 8)]
    (codeMat 266) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0641 :
    QuotientRankAtLeast (spanCodes [289, 160, 64, 16, 8, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 118), (160, 30), (64, 8), (16, 3), (8, 1), (4, 384), (3, 128)]
    (codeMat 98) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0642 :
    QuotientRankAtLeast (spanCodes [256, 144, 80, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (144, 325), (80, 326), (48, 256), (9, 432), (4, 8), (3, 24)]
    (codeMat 140) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0643 :
    QuotientRankAtLeast (spanCodes [265, 136, 72, 40, 25, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(265, 180), (136, 248), (72, 32), (40, 128), (25, 196), (5, 2), (3, 3)]
    (codeMat 177) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0644 :
    QuotientRankAtLeast (spanCodes [264, 137, 72, 41, 25, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(264, 240), (137, 101), (72, 40), (41, 197), (25, 69), (5, 3), (3, 1)]
    (codeMat 177) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0645 :
    QuotientRankAtLeast (spanCodes [264, 128, 65, 32, 16, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 29), (128, 8), (65, 360), (32, 3), (16, 1), (5, 384), (3, 256)]
    (codeMat 98) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0646 :
    QuotientRankAtLeast (spanCodes [264, 129, 64, 33, 17, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 413), (129, 264), (64, 360), (33, 387), (17, 257), (5, 384), (3, 256)]
    (codeMat 107) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0647 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 35, 19, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 91), (128, 54), (64, 63), (35, 88), (19, 112), (11, 120), (7, 128)]
    (codeMat 86) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0648 :
    QuotientRankAtLeast (spanCodes [256, 131, 64, 32, 19, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 8), (131, 240), (64, 40), (32, 1), (19, 198), (11, 197), (7, 128)]
    (codeMat 98) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0649 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 33, 16, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 139), (130, 9), (67, 119), (33, 480), (16, 8), (11, 392), (7, 360)]
    (codeMat 215) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
