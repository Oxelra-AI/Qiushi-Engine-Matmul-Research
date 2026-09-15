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

theorem plane282GenSource0030 :
    QuotientRankAtLeast (spanCodes [258, 226, 16, 10, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 135), (226, 275), (16, 45), (10, 12), (4, 2), (1, 1)]
    (codeMat 345) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane282GenSource0031 :
    QuotientRankAtLeast (spanCodes [258, 32, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 8, 2, 1] [(258, 136), (32, 2), (16, 3), (10, 28), (6, 8), (1, 32)]
    (codeMat 330) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_32_lb12

theorem plane282GenSource0032 :
    QuotientRankAtLeast (spanCodes [258, 34, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 8, 2, 1] [(258, 148), (34, 20), (16, 32), (10, 28), (4, 2), (1, 3)]
    (codeMat 401) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_32_lb12

theorem plane282GenSource0033 :
    QuotientRankAtLeast (spanCodes [258, 66, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 411), (66, 402), (38, 408), (16, 432), (10, 272), (1, 128)]
    (codeMat 95) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane282GenSource0034 :
    QuotientRankAtLeast (spanCodes [258, 64, 34, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 196), (64, 128), (34, 28), (16, 32), (10, 20), (4, 3), (1, 2)]
    (codeMat 273) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane282GenSource0035 :
    QuotientRankAtLeast (spanCodes [258, 66, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 68), (66, 196), (32, 8), (16, 32), (10, 28), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane282GenSource0036 :
    QuotientRankAtLeast (spanCodes [258, 130, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 139), (130, 130), (38, 136), (16, 128), (10, 272), (1, 432)]
    (codeMat 159) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane282GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 128, 32, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (128, 128), (32, 3), (16, 2), (10, 20), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane282GenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 130, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 88), (130, 216), (32, 1), (16, 3), (10, 28), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane282GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 8, 2, 1] [(258, 136), (130, 8), (64, 2), (16, 32), (10, 28), (1, 3)]
    (codeMat 165) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_32_lb12

end QiushiMatmul
