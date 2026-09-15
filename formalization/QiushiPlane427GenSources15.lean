import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0150 :
    QuotientRankAtLeast (spanCodes [264, 130, 72, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 381), (130, 9), (72, 130), (34, 104), (16, 8), (6, 256), (1, 128)]
    (codeMat 87) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0151 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 36, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(262, 34), (128, 2), (64, 1), (36, 432), (16, 130), (1, 9)]
    (codeMat 428) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane427GenSource0152 :
    QuotientRankAtLeast (spanCodes [260, 138, 72, 36, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 8), (138, 160), (72, 2), (36, 9), (16, 432), (1, 130)]
    (codeMat 494) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane427GenSource0153 :
    QuotientRankAtLeast (spanCodes [266, 138, 64, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 230), (138, 228), (64, 3), (34, 416), (16, 256), (6, 16), (1, 24)]
    (codeMat 140) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0154 :
    QuotientRankAtLeast (spanCodes [264, 136, 64, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 70), (136, 68), (64, 1), (34, 416), (16, 256), (6, 16), (1, 8)]
    (codeMat 140) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0155 :
    QuotientRankAtLeast (spanCodes [266, 128, 74, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(266, 117), (128, 1), (74, 118), (34, 104), (16, 8), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0156 :
    QuotientRankAtLeast (spanCodes [256, 136, 76, 36, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (136, 406), (76, 502), (36, 1), (16, 130), (2, 128), (1, 384)]
    (codeMat 99) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0157 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 196), (128, 3), (64, 2), (36, 32), (16, 216), (10, 80), (1, 128)]
    (codeMat 92) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0158 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 228), (130, 219), (66, 210), (36, 32), (16, 216), (10, 80), (1, 128)]
    (codeMat 95) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0159 :
    QuotientRankAtLeast (spanCodes [260, 132, 66, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 130), (132, 381), (66, 97), (36, 128), (16, 360), (10, 96), (1, 8)]
    (codeMat 206) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
