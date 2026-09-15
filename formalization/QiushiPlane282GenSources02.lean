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

theorem plane282GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 160, 70, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (160, 79), (70, 160), (16, 1), (10, 10), (1, 16)]
    (codeMat 330) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane282GenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 162, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 506), (162, 170), (68, 79), (16, 16), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane282GenSource0022 :
    QuotientRankAtLeast (spanCodes [258, 38, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(258, 430), (38, 46), (16, 45), (10, 12), (1, 32)]
    (codeMat 459) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane282GenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 68, 38, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 408), (68, 272), (38, 46), (16, 45), (10, 12), (1, 32)]
    (codeMat 331) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane282GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 134, 38, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 404), (134, 306), (38, 34), (16, 32), (10, 12), (1, 45)]
    (codeMat 403) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane282GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 160, 16, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 436), (160, 272), (16, 32), (10, 12), (6, 2), (1, 1)]
    (codeMat 401) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane282GenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 194, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(258, 418), (194, 34), (16, 45), (10, 12), (1, 32)]
    (codeMat 107) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane282GenSource0027 :
    QuotientRankAtLeast (spanCodes [258, 160, 98, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 408), (160, 272), (98, 318), (16, 32), (10, 12), (1, 45)]
    (codeMat 179) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane282GenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 16, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 440), (160, 272), (66, 14), (16, 32), (10, 12), (1, 1)]
    (codeMat 177) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane282GenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 226, 16, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 437), (226, 275), (16, 45), (10, 12), (6, 3), (1, 1)]
    (codeMat 473) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
