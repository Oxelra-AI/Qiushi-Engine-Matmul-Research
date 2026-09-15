import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0190 :
    QuotientRankAtLeast (spanCodes [258, 146, 64, 32, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 150), (146, 54), (64, 216), (32, 128), (10, 198), (4, 2), (1, 3)]
    (codeMat 177) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0191 :
    QuotientRankAtLeast (spanCodes [276, 128, 68, 48, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 127), (128, 8), (68, 23), (48, 384), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0192 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 37, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 235), (133, 276), (68, 414), (37, 387), (16, 2), (8, 3), (2, 130)]
    (codeMat 234) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0193 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 37, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 324), (68, 326), (37, 424), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane462GenSource0194 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (128, 2), (68, 196), (36, 216), (20, 208), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0195 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (128, 1), (68, 30), (37, 232), (21, 104), (8, 384), (2, 8)]
    (codeMat 140) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0196 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (129, 191), (68, 109), (36, 32), (20, 248), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0197 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (128, 54), (68, 100), (36, 8), (21, 240), (9, 32), (3, 128)]
    (codeMat 95) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0198 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 36, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 276), (128, 511), (68, 406), (36, 256), (21, 488), (9, 384), (3, 8)]
    (codeMat 206) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0199 :
    QuotientRankAtLeast (spanCodes [256, 129, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (129, 503), (68, 406), (36, 128), (20, 488), (9, 384), (3, 8)]
    (codeMat 207) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
