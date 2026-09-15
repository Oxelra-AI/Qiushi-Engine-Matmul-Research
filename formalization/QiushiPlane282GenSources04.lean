import QiushiPlane282GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit118From31
import QiushiMonoOrbit121From55
import QiushiMonoOrbit151From65
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit31FP
import QiushiStep98Orbit153Mono
import QiushiStep99Mono3032
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane282GenSource0040 :
    QuotientRankAtLeast (spanCodes [258, 194, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 43), (194, 34), (16, 432), (10, 272), (6, 40), (1, 32)]
    (codeMat 205) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane282GenSource0041 :
    QuotientRankAtLeast (spanCodes [258, 160, 98, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 387), (160, 413), (98, 156), (16, 360), (10, 96), (6, 384), (1, 256)]
    (codeMat 93) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane282GenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 22), (128, 2), (64, 1), (16, 128), (10, 80), (6, 32), (1, 8)]
    (codeMat 140) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane282GenSource0043 :
    QuotientRankAtLeast (spanCodes [258, 162, 98, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 383), (162, 149), (98, 156), (16, 360), (10, 96), (6, 128), (1, 256)]
    (codeMat 95) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane282GenSource0044 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 52), (130, 2), (64, 9), (16, 128), (10, 80), (4, 32), (1, 8)]
    (codeMat 141) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane282GenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 162, 96, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 246), (162, 413), (96, 148), (16, 360), (10, 96), (4, 384), (1, 256)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane282GenSource0046 :
    QuotientRankAtLeast (spanCodes [256, 196, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(256, 256), (196, 68), (16, 16), (8, 24), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane282GenSource0047 :
    QuotientRankAtLeast (spanCodes [256, 160, 100, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 68), (100, 228), (16, 1), (8, 3), (2, 8), (1, 24)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane282GenSource0048 :
    QuotientRankAtLeast (spanCodes [256, 164, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (164, 228), (96, 68), (16, 3), (8, 1), (2, 24), (1, 8)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane282GenSource0049 :
    QuotientRankAtLeast (spanCodes [258, 194, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 315), (194, 306), (34, 312), (16, 32), (10, 272), (1, 432)]
    (codeMat 214) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

end QiushiMatmul
