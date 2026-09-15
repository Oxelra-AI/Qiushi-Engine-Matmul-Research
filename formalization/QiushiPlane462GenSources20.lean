import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0200 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (133, 68), (68, 326), (36, 24), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane462GenSource0201 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 36, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 373), (132, 406), (68, 414), (36, 384), (16, 2), (8, 3), (2, 130)]
    (codeMat 226) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0202 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 198), (128, 130), (68, 197), (37, 240), (21, 208), (8, 40), (2, 128)]
    (codeMat 85) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0203 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 29), (128, 9), (68, 30), (36, 360), (20, 104), (8, 384), (2, 8)]
    (codeMat 141) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0204 :
    QuotientRankAtLeast (spanCodes [276, 148, 68, 36, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 483), (148, 28), (68, 150), (36, 256), (8, 130), (2, 3), (1, 2)]
    (codeMat 241) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0205 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 82), (128, 9), (64, 54), (34, 80), (16, 8), (10, 112), (4, 128)]
    (codeMat 86) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0206 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 35, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 96), (128, 256), (64, 384), (35, 509), (17, 148), (10, 150), (4, 360)]
    (codeMat 299) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0207 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 149), (131, 510), (64, 511), (35, 96), (18, 384), (10, 392), (4, 360)]
    (codeMat 213) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0208 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 112), (128, 216), (65, 32), (34, 198), (16, 3), (10, 196), (5, 128)]
    (codeMat 106) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0209 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 112), (129, 248), (65, 32), (34, 70), (17, 199), (10, 196), (5, 128)]
    (codeMat 107) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
