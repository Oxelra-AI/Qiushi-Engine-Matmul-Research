import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0160 :
    QuotientRankAtLeast (spanCodes [272, 145, 81, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 510), (145, 374), (81, 30), (48, 1), (8, 3), (5, 256), (2, 384)]
    (codeMat 106) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0161 :
    QuotientRankAtLeast (spanCodes [257, 128, 81, 32, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 265), (128, 511), (81, 21), (32, 8), (9, 360), (5, 256), (3, 128)]
    (codeMat 87) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0162 :
    QuotientRankAtLeast (spanCodes [256, 129, 80, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (129, 257), (80, 97), (33, 151), (9, 360), (4, 2), (3, 1)]
    (codeMat 369) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0163 :
    QuotientRankAtLeast (spanCodes [257, 128, 80, 32, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 150), (128, 511), (80, 227), (32, 130), (9, 256), (4, 2), (3, 3)]
    (codeMat 241) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0164 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 254), (144, 511), (80, 381), (48, 8), (9, 360), (4, 384), (3, 128)]
    (codeMat 85) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0165 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 163), (144, 1), (80, 324), (49, 160), (8, 256), (4, 24), (2, 8)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0166 :
    QuotientRankAtLeast (spanCodes [272, 145, 80, 48, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 136), (145, 28), (80, 480), (48, 128), (8, 256), (4, 1), (2, 3)]
    (codeMat 177) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0167 :
    QuotientRankAtLeast (spanCodes [256, 130, 82, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 511), (82, 28), (34, 392), (10, 224), (6, 384), (1, 256)]
    (codeMat 95) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane472GenSource0168 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (130, 2), (68, 68), (34, 168), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane472GenSource0169 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 385), (128, 384), (64, 128), (36, 511), (20, 503), (10, 406), (1, 130)]
    (codeMat 277) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
