import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0270 :
    QuotientRankAtLeast (spanCodes [275, 128, 83, 51, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(275, 461), (128, 1), (83, 463), (51, 493), (10, 118)]
    (codeMat 116) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0271 :
    QuotientRankAtLeast (spanCodes [274, 150, 66, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 246), (150, 29), (66, 97), (52, 232), (10, 96), (1, 8)]
    (codeMat 206) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0272 :
    QuotientRankAtLeast (spanCodes [272, 133, 80, 52, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(272, 497), (133, 255), (80, 490), (52, 496), (9, 16), (3, 320)]
    (codeMat 95) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0273 :
    QuotientRankAtLeast (spanCodes [275, 144, 65, 50, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(275, 397), (144, 32), (65, 128), (50, 295), (10, 294)]
    (codeMat 370) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane490GenSource0274 :
    QuotientRankAtLeast (spanCodes [275, 147, 80, 33, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(275, 116), (147, 246), (80, 245), (33, 96), (10, 232), (6, 128)]
    (codeMat 93) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0275 :
    QuotientRankAtLeast (spanCodes [275, 145, 66, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(275, 311), (145, 11), (66, 81), (49, 296), (10, 80), (6, 32)]
    (codeMat 206) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane490GenSource0276 :
    QuotientRankAtLeast (spanCodes [275, 131, 80, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(275, 107), (131, 453), (80, 170), (49, 283), (10, 191), (6, 192)]
    (codeMat 117) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane490GenSource0277 :
    QuotientRankAtLeast (spanCodes [275, 130, 81, 51, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 331), (130, 1), (81, 78), (51, 336), (10, 496), (5, 320)]
    (codeMat 93) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0278 :
    QuotientRankAtLeast (spanCodes [275, 130, 80, 48, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 337), (130, 260), (80, 255), (48, 320), (10, 480), (7, 16)]
    (codeMat 143) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0279 :
    QuotientRankAtLeast (spanCodes [275, 129, 83, 48, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 331), (129, 446), (83, 79), (48, 320), (10, 496), (7, 16)]
    (codeMat 142) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
