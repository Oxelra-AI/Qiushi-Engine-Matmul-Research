import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0250 :
    QuotientRankAtLeast (spanCodes [273, 144, 64, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(273, 140), (144, 8), (64, 2), (8, 3), (2, 32)]
    (codeMat 102) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0251 :
    QuotientRankAtLeast (spanCodes [257, 192, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 164), (192, 2), (16, 8), (8, 9), (2, 32)]
    (codeMat 98) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0252 :
    QuotientRankAtLeast (spanCodes [272, 145, 64, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(272, 175), (145, 41), (64, 2), (9, 3), (3, 32)]
    (codeMat 103) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0253 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 3), (134, 35), (70, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0254 :
    QuotientRankAtLeast (spanCodes [256, 133, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (133, 35), (69, 34), (19, 462), (10, 441)]
    (codeMat 428) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0255 :
    QuotientRankAtLeast (spanCodes [256, 167, 103, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (167, 84), (103, 85), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0256 :
    QuotientRankAtLeast (spanCodes [256, 165, 101, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 3), (165, 410), (101, 411), (19, 441), (10, 119)]
    (codeMat 380) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0257 :
    QuotientRankAtLeast (spanCodes [260, 165, 97, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 27), (165, 239), (97, 245), (20, 480), (9, 320), (3, 16)]
    (codeMat 204) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0258 :
    QuotientRankAtLeast (spanCodes [260, 161, 101, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (161, 95), (101, 69), (20, 496), (9, 320), (3, 16)]
    (codeMat 205) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0259 :
    QuotientRankAtLeast (spanCodes [256, 134, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (134, 34), (64, 1), (19, 441), (10, 119)]
    (codeMat 428) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
