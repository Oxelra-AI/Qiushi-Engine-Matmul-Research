import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 142, 72, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 432), (142, 443), (72, 128), (40, 32), (16, 40), (1, 130)]
    (codeMat 407) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0201 :
    QuotientRankAtLeast (spanCodes [264, 142, 64, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(264, 400), (142, 403), (64, 128), (40, 32), (16, 40), (1, 130)]
    (codeMat 277) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0202 :
    QuotientRankAtLeast (spanCodes [264, 142, 72, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(264, 304), (142, 313), (72, 128), (32, 32), (16, 40), (1, 130)]
    (codeMat 407) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0203 :
    QuotientRankAtLeast (spanCodes [256, 142, 64, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 1), (142, 273), (64, 2), (32, 8), (16, 40), (1, 130)]
    (codeMat 340) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0204 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 2), (70, 68), (34, 184), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0205 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (130, 2), (68, 68), (34, 168), (16, 16), (10, 160), (1, 256)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0206 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0207 :
    QuotientRankAtLeast (spanCodes [260, 162, 64, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(260, 8), (162, 80), (64, 5), (16, 128), (8, 2), (1, 4)]
    (codeMat 85) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0208 :
    QuotientRankAtLeast (spanCodes [384, 70, 32, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(384, 8), (70, 80), (32, 4), (16, 5), (8, 2), (1, 128)]
    (codeMat 98) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0209 :
    QuotientRankAtLeast (spanCodes [258, 128, 106, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 400), (128, 128), (106, 403), (16, 130), (6, 32), (1, 40)]
    (codeMat 270) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

end QiushiMatmul
