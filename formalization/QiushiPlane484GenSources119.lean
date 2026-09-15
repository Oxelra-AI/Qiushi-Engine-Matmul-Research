import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1190 :
    QuotientRankAtLeast (spanCodes [257, 132, 65, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (132, 70), (65, 2), (37, 184), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1191 :
    QuotientRankAtLeast (spanCodes [256, 133, 65, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (133, 70), (65, 2), (37, 168), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1192 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 198), (128, 1), (64, 3), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 84) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1193 :
    QuotientRankAtLeast (spanCodes [256, 132, 69, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (132, 284), (69, 381), (33, 488), (16, 256), (9, 360), (3, 8)]
    (codeMat 143) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1194 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 228), (128, 9), (65, 219), (32, 32), (16, 8), (9, 216), (3, 128)]
    (codeMat 86) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1195 :
    QuotientRankAtLeast (spanCodes [260, 133, 65, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (133, 508), (65, 1), (32, 128), (16, 256), (9, 8), (3, 360)]
    (codeMat 157) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1196 :
    QuotientRankAtLeast (spanCodes [260, 129, 69, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (129, 258), (69, 70), (32, 8), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1197 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(261, 70), (129, 131), (65, 1), (37, 112), (16, 216), (9, 8), (3, 128)]
    (codeMat 93) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1198 :
    QuotientRankAtLeast (spanCodes [256, 133, 64, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (133, 224), (64, 128), (37, 150), (16, 511), (9, 2), (3, 360)]
    (codeMat 299) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1199 :
    QuotientRankAtLeast (spanCodes [257, 132, 64, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 406), (132, 97), (64, 130), (37, 150), (16, 360), (9, 2), (3, 511)]
    (codeMat 491) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
