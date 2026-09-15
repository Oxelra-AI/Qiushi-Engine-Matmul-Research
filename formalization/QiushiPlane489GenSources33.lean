import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0330 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 68), (128, 1), (66, 70), (32, 32), (16, 8), (10, 112), (5, 128)]
    (codeMat 84) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0331 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (130, 8), (65, 32), (32, 2), (16, 1), (10, 68), (4, 128)]
    (codeMat 106) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0332 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 52, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(257, 42), (129, 10), (65, 2), (52, 283), (9, 128), (3, 9)]
    (codeMat 229) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane489GenSource0333 :
    QuotientRankAtLeast (spanCodes [257, 144, 65, 37, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(257, 306), (144, 3), (65, 130), (37, 274), (9, 128), (3, 9)]
    (codeMat 254) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane489GenSource0334 :
    QuotientRankAtLeast (spanCodes [257, 145, 65, 36, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(257, 139), (145, 400), (65, 130), (36, 3), (9, 2), (3, 432)]
    (codeMat 443) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane489GenSource0335 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 353), (133, 413), (65, 9), (37, 97), (21, 414), (9, 8), (3, 130)]
    (codeMat 478) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0336 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 138), (133, 276), (65, 8), (36, 3), (20, 363), (9, 1), (3, 511)]
    (codeMat 491) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0337 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 71), (129, 69), (64, 1), (33, 440), (20, 168), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane489GenSource0338 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 71), (129, 258), (68, 70), (33, 440), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane489GenSource0339 :
    QuotientRankAtLeast (spanCodes [257, 144, 80, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 387), (144, 511), (80, 381), (49, 352), (9, 360), (5, 384), (3, 128)]
    (codeMat 85) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
