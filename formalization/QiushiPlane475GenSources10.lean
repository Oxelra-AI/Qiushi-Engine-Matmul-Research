import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0100 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 33, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (132, 363), (65, 1), (33, 138), (21, 276), (9, 8), (3, 511)]
    (codeMat 477) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane475GenSource0101 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 326), (133, 327), (64, 3), (32, 432), (21, 184), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane475GenSource0102 :
    QuotientRankAtLeast (spanCodes [256, 129, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (129, 503), (68, 406), (36, 128), (20, 488), (9, 384), (3, 8)]
    (codeMat 207) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane475GenSource0103 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 100), (129, 237), (65, 54), (33, 160), (18, 40), (10, 240), (5, 128)]
    (codeMat 94) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane475GenSource0104 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 34, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 196), (129, 70), (66, 71), (34, 160), (17, 112), (10, 120), (6, 128)]
    (codeMat 93) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane475GenSource0105 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 259), (130, 2), (64, 325), (32, 24), (16, 16), (10, 168), (7, 256)]
    (codeMat 85) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane475GenSource0106 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 360), (64, 3), (32, 8), (19, 414), (10, 373), (7, 511)]
    (codeMat 468) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane475GenSource0107 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (129, 327), (65, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 92) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane475GenSource0108 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 198), (128, 3), (66, 199), (34, 240), (18, 216), (10, 248), (7, 128)]
    (codeMat 84) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane475GenSource0109 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (131, 326), (64, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 85) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
