import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0090 :
    QuotientRankAtLeast (spanCodes [257, 131, 34, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 252), (131, 224), (34, 10), (18, 8), (10, 136), (6, 3)]
    (codeMat 275) (codeMat 124) (codeMat 124) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0091 :
    QuotientRankAtLeast (spanCodes [259, 129, 32, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 96), (129, 232), (32, 1), (16, 3), (10, 30), (4, 8)]
    (codeMat 330) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0092 :
    QuotientRankAtLeast (spanCodes [256, 161, 64, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (161, 87), (64, 3), (20, 493), (10, 411)]
    (codeMat 124) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane456GenSource0093 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (160, 160), (68, 68), (20, 436), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0094 :
    QuotientRankAtLeast (spanCodes [288, 161, 99, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(288, 27), (161, 267), (99, 379), (19, 463), (10, 446), (7, 16)]
    (codeMat 335) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane456GenSource0095 :
    QuotientRankAtLeast (spanCodes [259, 161, 66, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 272), (161, 212), (66, 112), (19, 463), (10, 113), (7, 16)]
    (codeMat 334) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane456GenSource0096 :
    QuotientRankAtLeast (spanCodes [320, 161, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(320, 32), (161, 492), (19, 119), (10, 441), (7, 1)]
    (codeMat 305) (codeMat 346) (codeMat 459) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane456GenSource0097 :
    QuotientRankAtLeast (spanCodes [289, 161, 101, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(289, 463), (161, 271), (101, 97), (20, 420), (9, 260), (3, 432)]
    (codeMat 214) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane456GenSource0098 :
    QuotientRankAtLeast (spanCodes [292, 161, 96, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 27), (161, 271), (96, 437), (20, 480), (9, 320), (3, 16)]
    (codeMat 206) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0099 :
    QuotientRankAtLeast (spanCodes [325, 161, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(325, 384), (161, 85), (20, 10), (8, 32), (2, 1)]
    (codeMat 337) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

end QiushiMatmul
