import QiushiPlane413GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit271From120
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane413GenSource0040 :
    QuotientRankAtLeast (spanCodes [468, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [336, 32, 2, 1] [(468, 337), (32, 32), (2, 2), (1, 3)]
    (codeMat 337) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit271_lb15_mono

theorem plane413GenSource0041 :
    QuotientRankAtLeast (spanCodes [272, 144, 32, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(272, 208), (144, 216), (32, 128), (4, 2), (2, 3), (1, 4)]
    (codeMat 161) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane413GenSource0042 :
    QuotientRankAtLeast (spanCodes [272, 128, 32, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(272, 80), (128, 8), (32, 128), (4, 2), (2, 1), (1, 4)]
    (codeMat 161) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane413GenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 2), (132, 20), (64, 1), (32, 128), (12, 80), (2, 32), (1, 8)]
    (codeMat 140) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane413GenSource0044 :
    QuotientRankAtLeast (spanCodes [268, 132, 72, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 484), (132, 162), (72, 3), (32, 256), (20, 160), (2, 16), (1, 24)]
    (codeMat 142) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane413GenSource0045 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 2), (132, 52), (68, 61), (32, 128), (28, 80), (2, 32), (1, 40)]
    (codeMat 141) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane413GenSource0046 :
    QuotientRankAtLeast (spanCodes [268, 128, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(268, 228), (128, 2), (64, 3), (32, 256), (20, 160), (2, 16), (1, 24)]
    (codeMat 140) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane413GenSource0047 :
    QuotientRankAtLeast (spanCodes [260, 136, 76, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 130), (136, 100), (76, 61), (32, 128), (28, 80), (2, 32), (1, 40)]
    (codeMat 143) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane413GenSource0048 :
    QuotientRankAtLeast (spanCodes [256, 148, 68, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 130), (148, 20), (68, 81), (32, 128), (12, 80), (2, 32), (1, 8)]
    (codeMat 142) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
