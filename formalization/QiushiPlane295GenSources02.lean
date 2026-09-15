import QiushiPlane295GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep99Orbit34Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane295GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 192, 32, 18, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 20, 8, 2, 1] [(258, 336), (192, 8), (32, 2), (18, 325), (10, 324), (1, 256)]
    (codeMat 98) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit34_lb14_unconditional

theorem plane295GenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 130, 32, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (130, 216), (32, 2), (16, 3), (10, 28), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane295GenSource0022 :
    QuotientRankAtLeast (spanCodes [272, 128, 66, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 68), (128, 325), (66, 170), (32, 256), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane295GenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 148), (68, 149), (32, 128), (16, 256), (10, 96), (1, 360)]
    (codeMat 156) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 134, 68, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 373), (134, 414), (68, 227), (32, 3), (18, 360), (10, 362), (1, 511)]
    (codeMat 482) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (132, 224), (70, 264), (32, 3), (18, 511), (10, 509), (1, 360)]
    (codeMat 354) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (130, 256), (70, 393), (32, 130), (20, 406), (10, 227), (1, 511)]
    (codeMat 351) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0027 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 228), (130, 219), (66, 210), (32, 32), (18, 216), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane295GenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 196), (128, 3), (64, 2), (32, 32), (18, 216), (10, 208), (1, 128)]
    (codeMat 84) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane295GenSource0029 :
    QuotientRankAtLeast (spanCodes [256, 132, 70, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (132, 404), (70, 245), (32, 128), (16, 256), (10, 96), (1, 360)]
    (codeMat 158) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
