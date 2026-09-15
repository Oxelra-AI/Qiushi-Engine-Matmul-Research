import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0190 :
    QuotientRankAtLeast (spanCodes [260, 130, 68, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (130, 1), (68, 362), (36, 130), (16, 8), (14, 227), (1, 511)]
    (codeMat 405) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0191 :
    QuotientRankAtLeast (spanCodes [256, 132, 70, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (132, 126), (70, 404), (36, 8), (16, 511), (14, 276), (1, 130)]
    (codeMat 415) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0192 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 126), (130, 9), (70, 278), (36, 511), (16, 8), (14, 406), (1, 130)]
    (codeMat 407) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0193 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (134, 23), (64, 9), (36, 130), (16, 511), (14, 97), (1, 8)]
    (codeMat 397) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0194 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (128, 2), (64, 1), (36, 511), (16, 130), (14, 105), (1, 8)]
    (codeMat 396) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0195 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 2), (66, 149), (36, 8), (16, 130), (14, 284), (1, 511)]
    (codeMat 412) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0196 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (134, 70), (68, 324), (36, 8), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0197 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (128, 9), (68, 413), (36, 384), (16, 8), (10, 96), (1, 360)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0198 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (132, 326), (70, 68), (36, 24), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0199 :
    QuotientRankAtLeast (spanCodes [258, 192, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 112), (192, 128), (32, 9), (16, 54), (10, 20), (4, 8), (1, 32)]
    (codeMat 267) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
