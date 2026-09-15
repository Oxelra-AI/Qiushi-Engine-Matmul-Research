import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0190 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 149), (128, 2), (66, 150), (33, 227), (16, 130), (10, 406), (4, 511)]
    (codeMat 412) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0191 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 104), (130, 128), (65, 384), (35, 97), (16, 130), (10, 406), (4, 8)]
    (codeMat 335) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0192 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 97), (131, 284), (65, 511), (34, 96), (16, 256), (10, 480), (4, 8)]
    (codeMat 142) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0193 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (131, 28), (67, 31), (34, 96), (16, 256), (10, 480), (4, 8)]
    (codeMat 140) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0194 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 353), (131, 413), (65, 360), (34, 227), (19, 414), (10, 235), (7, 130)]
    (codeMat 470) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0195 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 235), (128, 130), (65, 511), (33, 224), (18, 128), (10, 488), (6, 8)]
    (codeMat 207) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0196 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (128, 2), (66, 23), (33, 224), (18, 128), (10, 488), (6, 8)]
    (codeMat 204) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0197 :
    QuotientRankAtLeast (spanCodes [322, 130, 34, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(322, 88), (130, 216), (34, 28), (16, 3), (10, 29), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane456GenSource0198 :
    QuotientRankAtLeast (spanCodes [322, 128, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(322, 208), (128, 128), (32, 54), (18, 2), (10, 61), (6, 32), (1, 40)]
    (codeMat 267) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane456GenSource0199 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 246), (130, 128), (66, 137), (35, 97), (18, 130), (10, 138), (6, 511)]
    (codeMat 342) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
