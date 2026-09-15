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

theorem plane456GenSource0130 :
    QuotientRankAtLeast (spanCodes [327, 128, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(327, 34), (128, 32), (33, 118), (20, 440), (10, 463)]
    (codeMat 299) (codeMat 345) (codeMat 345) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane456GenSource0131 :
    QuotientRankAtLeast (spanCodes [354, 161, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(354, 500), (161, 84), (16, 1), (10, 11), (4, 32)]
    (codeMat 330) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane456GenSource0132 :
    QuotientRankAtLeast (spanCodes [288, 161, 67, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 1), (161, 254), (67, 420), (17, 176), (10, 160), (5, 320)]
    (codeMat 94) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0133 :
    QuotientRankAtLeast (spanCodes [291, 161, 64, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(291, 127), (161, 442), (64, 260), (17, 272), (10, 160), (5, 192)]
    (codeMat 85) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane456GenSource0134 :
    QuotientRankAtLeast (spanCodes [262, 134, 70, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 104), (134, 96), (70, 105), (39, 252), (20, 224), (10, 255)]
    (codeMat 124) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0135 :
    QuotientRankAtLeast (spanCodes [259, 131, 70, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 252), (131, 245), (70, 126), (34, 104), (20, 96), (10, 232)]
    (codeMat 159) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane456GenSource0136 :
    QuotientRankAtLeast (spanCodes [257, 128, 71, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 353), (128, 27), (71, 175), (33, 97), (20, 479), (10, 430)]
    (codeMat 415) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane456GenSource0137 :
    QuotientRankAtLeast (spanCodes [262, 129, 65, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 496), (129, 336), (65, 16), (32, 1), (20, 79), (10, 506)]
    (codeMat 298) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0138 :
    QuotientRankAtLeast (spanCodes [289, 161, 65, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(289, 352), (161, 379), (65, 1), (19, 446), (10, 113), (7, 16)]
    (codeMat 461) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane456GenSource0139 :
    QuotientRankAtLeast (spanCodes [259, 161, 97, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 118), (161, 157), (97, 148), (17, 104), (10, 96), (5, 128)]
    (codeMat 95) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
