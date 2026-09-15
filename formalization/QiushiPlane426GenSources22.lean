import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep99Mono3032
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0220 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 8, 2, 1] [(272, 148), (128, 2), (80, 20), (8, 32), (2, 1), (1, 8)]
    (codeMat 161) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_32_lb12

theorem plane426GenSource0221 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (128, 8), (68, 22), (20, 70), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0222 :
    QuotientRankAtLeast (spanCodes [260, 164, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (164, 246), (96, 97), (20, 29), (8, 8), (2, 3), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0223 :
    QuotientRankAtLeast (spanCodes [260, 160, 100, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (160, 224), (100, 119), (20, 31), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0224 :
    QuotientRankAtLeast (spanCodes [256, 162, 98, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (162, 413), (98, 412), (16, 360), (10, 96), (6, 384), (1, 256)]
    (codeMat 92) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0225 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (132, 30), (68, 22), (20, 198), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0226 :
    QuotientRankAtLeast (spanCodes [260, 160, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (160, 227), (96, 97), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0227 :
    QuotientRankAtLeast (spanCodes [272, 132, 80, 52, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 252), (132, 224), (80, 404), (52, 259), (8, 130), (2, 256), (1, 128)]
    (codeMat 107) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0228 :
    QuotientRankAtLeast (spanCodes [272, 130, 82, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 490), (130, 511), (82, 28), (48, 360), (10, 224), (4, 128), (1, 256)]
    (codeMat 95) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0229 :
    QuotientRankAtLeast (spanCodes [272, 144, 66, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(272, 228), (144, 63), (66, 113), (50, 248), (10, 120), (4, 32), (1, 8)]
    (codeMat 143) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
