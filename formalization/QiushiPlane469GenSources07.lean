import QiushiPlane469GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit231Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit67Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit179Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane469GenSource0070 :
    QuotientRankAtLeast (spanCodes [256, 160, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 84, 32, 10, 1] [(256, 1), (160, 10), (84, 84), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit179_lb15_wc

theorem plane469GenSource0071 :
    QuotientRankAtLeast (spanCodes [256, 161, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(256, 1), (161, 140), (84, 98), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane469GenSource0072 :
    QuotientRankAtLeast (spanCodes [258, 147, 82, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 368), (147, 453), (82, 21), (49, 283), (10, 191), (6, 192)]
    (codeMat 103) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane469GenSource0073 :
    QuotientRankAtLeast (spanCodes [258, 147, 82, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(258, 385), (147, 191), (82, 378), (51, 368), (10, 464), (6, 384)]
    (codeMat 85) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane469GenSource0074 :
    QuotientRankAtLeast (spanCodes [256, 164, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 1), (164, 10), (84, 116), (8, 384), (2, 32)]
    (codeMat 92) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane469GenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 128, 80, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 10), (128, 1), (80, 79), (35, 160), (10, 496), (4, 16)]
    (codeMat 204) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane469GenSource0076 :
    QuotientRankAtLeast (spanCodes [258, 130, 80, 33, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 68), (130, 260), (80, 160), (33, 78), (10, 436), (4, 1)]
    (codeMat 305) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane469GenSource0077 :
    QuotientRankAtLeast (spanCodes [258, 129, 68, 33, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 164, 68, 16, 10, 1] [(258, 440), (129, 328), (68, 224), (33, 263), (16, 1), (10, 68)]
    (codeMat 106) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit67_lb15_unconditional

theorem plane469GenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 135, 71, 36, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 453), (135, 196), (71, 197), (36, 16), (19, 446), (10, 113)]
    (codeMat 348) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane469GenSource0079 :
    QuotientRankAtLeast (spanCodes [258, 133, 66, 35, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 21), (133, 11), (66, 20), (35, 475), (22, 191), (10, 420)]
    (codeMat 236) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
