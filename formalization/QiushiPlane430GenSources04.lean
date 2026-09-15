import QiushiPlane430GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane430GenSource0040 :
    QuotientRankAtLeast (spanCodes [266, 138, 64, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 230), (138, 228), (64, 3), (34, 416), (16, 256), (6, 16), (1, 24)]
    (codeMat 140) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane430GenSource0041 :
    QuotientRankAtLeast (spanCodes [256, 138, 72, 42, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (138, 484), (72, 3), (42, 416), (16, 256), (6, 8), (1, 24)]
    (codeMat 142) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane430GenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 136, 72, 42, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 487), (136, 324), (72, 1), (42, 416), (16, 256), (6, 24), (1, 8)]
    (codeMat 142) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane430GenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (128, 2), (66, 20), (34, 80), (16, 128), (4, 8), (1, 32)]
    (codeMat 140) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane430GenSource0044 :
    QuotientRankAtLeast (spanCodes [264, 128, 74, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(264, 68), (128, 130), (74, 21), (42, 80), (16, 128), (4, 32), (1, 40)]
    (codeMat 142) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane430GenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 2), (70, 68), (34, 184), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane430GenSource0046 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (132, 100), (68, 82), (32, 8), (16, 32), (12, 80), (1, 128)]
    (codeMat 86) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane430GenSource0047 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane430GenSource0048 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (132, 385), (64, 128), (36, 8), (16, 511), (14, 276), (1, 130)]
    (codeMat 285) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane430GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 3), (134, 196), (64, 130), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
