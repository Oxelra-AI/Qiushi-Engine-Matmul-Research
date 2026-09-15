import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0180 :
    QuotientRankAtLeast (spanCodes [272, 128, 66, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 284), (128, 511), (66, 149), (50, 31), (10, 23), (6, 3), (1, 2)]
    (codeMat 465) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0181 :
    QuotientRankAtLeast (spanCodes [257, 145, 64, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 81), (145, 20), (64, 130), (33, 80), (8, 128), (4, 8), (2, 32)]
    (codeMat 142) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0182 :
    QuotientRankAtLeast (spanCodes [273, 129, 64, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 98), (129, 118), (64, 9), (49, 96), (8, 8), (4, 128), (2, 384)]
    (codeMat 86) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0183 :
    QuotientRankAtLeast (spanCodes [256, 145, 65, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 219), (145, 52), (65, 130), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 143) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0184 :
    QuotientRankAtLeast (spanCodes [272, 129, 65, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 235), (129, 502), (65, 9), (49, 104), (8, 8), (5, 128), (2, 384)]
    (codeMat 87) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0185 :
    QuotientRankAtLeast (spanCodes [256, 145, 65, 32, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 130), (145, 30), (65, 219), (32, 128), (9, 216), (5, 8), (3, 40)]
    (codeMat 142) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0186 :
    QuotientRankAtLeast (spanCodes [273, 128, 65, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 355), (128, 511), (65, 9), (49, 352), (9, 8), (5, 128), (3, 384)]
    (codeMat 94) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0187 :
    QuotientRankAtLeast (spanCodes [257, 144, 64, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 81), (144, 54), (64, 219), (33, 88), (9, 216), (4, 8), (3, 40)]
    (codeMat 143) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0188 :
    QuotientRankAtLeast (spanCodes [272, 129, 64, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 490), (129, 127), (64, 9), (48, 360), (9, 8), (4, 128), (3, 384)]
    (codeMat 95) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0189 :
    QuotientRankAtLeast (spanCodes [272, 130, 66, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 392), (130, 511), (66, 151), (48, 8), (10, 23), (6, 1), (1, 2)]
    (codeMat 401) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
