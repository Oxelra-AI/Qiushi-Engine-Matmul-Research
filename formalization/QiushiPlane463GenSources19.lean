import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0190 :
    QuotientRankAtLeast (spanCodes [256, 144, 66, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 219), (144, 54), (66, 121), (34, 240), (10, 112), (6, 40), (1, 8)]
    (codeMat 143) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane463GenSource0191 :
    QuotientRankAtLeast (spanCodes [273, 128, 64, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 158), (128, 3), (64, 1), (48, 360), (9, 8), (4, 384), (3, 128)]
    (codeMat 92) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0192 :
    QuotientRankAtLeast (spanCodes [272, 129, 64, 49, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 373), (129, 104), (64, 8), (49, 131), (9, 1), (4, 384), (3, 256)]
    (codeMat 99) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0193 :
    QuotientRankAtLeast (spanCodes [273, 128, 65, 48, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 253), (128, 360), (65, 8), (48, 130), (9, 1), (5, 384), (3, 256)]
    (codeMat 107) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0194 :
    QuotientRankAtLeast (spanCodes [273, 129, 64, 48, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 116), (129, 96), (64, 8), (48, 2), (8, 1), (4, 384), (2, 256)]
    (codeMat 98) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0195 :
    QuotientRankAtLeast (spanCodes [256, 146, 66, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 130), (146, 54), (66, 113), (32, 128), (10, 112), (6, 32), (1, 8)]
    (codeMat 142) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane463GenSource0196 :
    QuotientRankAtLeast (spanCodes [258, 146, 64, 32, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 150), (146, 54), (64, 216), (32, 128), (10, 198), (4, 2), (1, 3)]
    (codeMat 177) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane463GenSource0197 :
    QuotientRankAtLeast (spanCodes [276, 128, 68, 48, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 127), (128, 8), (68, 23), (48, 384), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0198 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (134, 70), (68, 324), (36, 8), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0199 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 373), (132, 284), (68, 414), (36, 3), (17, 149), (8, 360), (2, 511)]
    (codeMat 491) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
