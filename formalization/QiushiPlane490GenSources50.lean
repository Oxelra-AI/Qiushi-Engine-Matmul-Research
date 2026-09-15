import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0500 :
    QuotientRankAtLeast (spanCodes [256, 133, 65, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (133, 70), (65, 2), (37, 168), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0501 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 327), (64, 3), (33, 424), (20, 184), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0502 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (128, 3), (68, 510), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 212) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0503 :
    QuotientRankAtLeast (spanCodes [260, 128, 65, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (128, 325), (65, 1), (36, 24), (20, 424), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0504 :
    QuotientRankAtLeast (spanCodes [260, 132, 69, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 130), (132, 139), (69, 278), (36, 128), (20, 136), (9, 384), (3, 360)]
    (codeMat 214) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0505 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (128, 9), (65, 219), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 86) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0506 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 70), (64, 2), (36, 8), (16, 432), (9, 16), (3, 256)]
    (codeMat 92) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0507 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 1), (68, 148), (36, 128), (16, 8), (9, 256), (3, 360)]
    (codeMat 212) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0508 :
    QuotientRankAtLeast (spanCodes [261, 133, 65, 33, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 119), (133, 287), (65, 9), (33, 503), (21, 284), (9, 8), (3, 130)]
    (codeMat 478) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0509 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 326), (133, 327), (64, 3), (32, 432), (21, 184), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
