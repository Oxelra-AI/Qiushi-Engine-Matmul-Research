import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0120 :
    QuotientRankAtLeast (spanCodes [256, 181, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 511), (181, 478), (84, 116), (9, 384), (3, 32)]
    (codeMat 87) (codeMat 500) (codeMat 94) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane470GenSource0121 :
    QuotientRankAtLeast (spanCodes [259, 132, 64, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 176), (132, 480), (64, 320), (39, 436), (20, 507), (10, 437)]
    (codeMat 299) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane470GenSource0122 :
    QuotientRankAtLeast (spanCodes [259, 129, 83, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(259, 333), (129, 81), (83, 11), (49, 338), (10, 91), (7, 365)]
    (codeMat 174) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane470GenSource0123 :
    QuotientRankAtLeast (spanCodes [259, 146, 83, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(259, 338), (146, 1), (83, 90), (34, 113), (10, 81), (7, 365)]
    (codeMat 279) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane470GenSource0124 :
    QuotientRankAtLeast (spanCodes [259, 130, 82, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 191), (130, 27), (82, 430), (51, 96), (10, 368), (6, 256)]
    (codeMat 94) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane470GenSource0125 :
    QuotientRankAtLeast (spanCodes [259, 146, 82, 35, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 96), (146, 27), (82, 283), (35, 97), (10, 479), (6, 16)]
    (codeMat 270) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane470GenSource0126 :
    QuotientRankAtLeast (spanCodes [259, 144, 82, 33, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 228), (144, 1), (82, 446), (33, 160), (10, 496), (6, 320)]
    (codeMat 94) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane470GenSource0127 :
    QuotientRankAtLeast (spanCodes [259, 131, 81, 49, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(259, 20), (131, 148), (81, 366), (49, 484), (10, 507), (5, 260)]
    (codeMat 102) (codeMat 249) (codeMat 425) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane470GenSource0128 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 16, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 256), (164, 196), (68, 96), (16, 27), (9, 1), (3, 16)]
    (codeMat 267) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane470GenSource0129 :
    QuotientRankAtLeast (spanCodes [258, 164, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (164, 79), (70, 160), (18, 1), (10, 26), (1, 16)]
    (codeMat 331) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
