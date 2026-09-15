import QiushiPlane469GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit67Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane469GenSource0100 :
    QuotientRankAtLeast (spanCodes [258, 133, 64, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 367), (133, 222), (64, 1), (39, 420), (20, 191), (10, 356)]
    (codeMat 244) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane469GenSource0101 :
    QuotientRankAtLeast (spanCodes [258, 134, 65, 37, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 175), (134, 378), (65, 27), (37, 430), (21, 446), (10, 479)]
    (codeMat 407) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane469GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 129, 70, 37, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(258, 81), (129, 463), (70, 251), (37, 453), (18, 1), (10, 385)]
    (codeMat 163) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane469GenSource0103 :
    QuotientRankAtLeast (spanCodes [258, 131, 82, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 433), (131, 127), (82, 283), (51, 272), (10, 420), (6, 432)]
    (codeMat 213) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane469GenSource0104 :
    QuotientRankAtLeast (spanCodes [258, 129, 82, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(258, 289), (129, 367), (82, 191), (49, 10), (10, 21), (6, 1)]
    (codeMat 465) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane469GenSource0105 :
    QuotientRankAtLeast (spanCodes [258, 145, 80, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 462), (145, 367), (80, 21), (35, 160), (10, 464), (4, 432)]
    (codeMat 214) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane469GenSource0106 :
    QuotientRankAtLeast (spanCodes [256, 180, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(256, 1), (180, 126), (84, 116), (8, 32), (2, 384)]
    (codeMat 84) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane469GenSource0107 :
    QuotientRankAtLeast (spanCodes [258, 129, 67, 33, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 164, 68, 16, 10, 1] [(258, 440), (129, 240), (67, 344), (33, 263), (23, 262), (10, 323)]
    (codeMat 99) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit67_lb15_unconditional

theorem plane469GenSource0108 :
    QuotientRankAtLeast (spanCodes [258, 129, 64, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 436), (129, 78), (64, 1), (34, 176), (20, 160), (10, 496)]
    (codeMat 156) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane469GenSource0109 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (131, 336), (64, 16), (32, 1), (20, 79), (10, 506)]
    (codeMat 354) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
