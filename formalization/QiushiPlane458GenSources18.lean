import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0180 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (129, 392), (68, 488), (32, 130), (20, 406), (9, 511), (3, 8)]
    (codeMat 335) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0181 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (128, 2), (66, 21), (35, 227), (18, 130), (10, 381), (6, 8)]
    (codeMat 460) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0182 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 182), (129, 228), (65, 63), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 94) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0183 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 373), (131, 406), (67, 276), (34, 29), (17, 22), (10, 20), (5, 8)]
    (codeMat 459) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0184 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 112), (129, 248), (65, 32), (34, 70), (17, 199), (10, 196), (5, 128)]
    (codeMat 107) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0185 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 259), (128, 325), (67, 327), (33, 280), (17, 168), (10, 184), (5, 256)]
    (codeMat 93) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane458GenSource0186 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 257), (131, 327), (64, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 93) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane458GenSource0187 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 393), (130, 9), (66, 265), (35, 284), (16, 8), (10, 97), (4, 511)]
    (codeMat 279) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0188 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (129, 191), (68, 237), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0189 :
    QuotientRankAtLeast (spanCodes [257, 132, 69, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 373), (132, 105), (69, 414), (36, 360), (20, 104), (8, 384), (2, 8)]
    (codeMat 142) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
