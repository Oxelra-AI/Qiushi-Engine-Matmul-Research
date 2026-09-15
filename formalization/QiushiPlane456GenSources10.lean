import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit146Dispatch
import QiushiWcOrbit165Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0100 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (129, 160), (66, 176), (32, 1), (20, 78), (10, 436)]
    (codeMat 298) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0101 :
    QuotientRankAtLeast (spanCodes [256, 131, 66, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 1), (131, 437), (66, 363), (34, 352), (20, 96), (10, 368)]
    (codeMat 212) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane456GenSource0102 :
    QuotientRankAtLeast (spanCodes [263, 131, 69, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(263, 30), (131, 366), (69, 235), (34, 400), (20, 272), (10, 148)]
    (codeMat 158) (codeMat 249) (codeMat 425) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane456GenSource0103 :
    QuotientRankAtLeast (spanCodes [327, 134, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(327, 97), (134, 308), (39, 30), (20, 20), (10, 31)]
    (codeMat 395) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane456GenSource0104 :
    QuotientRankAtLeast (spanCodes [263, 130, 69, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(263, 69), (130, 384), (69, 452), (35, 357), (20, 308), (10, 414)]
    (codeMat 340) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane456GenSource0105 :
    QuotientRankAtLeast (spanCodes [263, 131, 68, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(263, 11), (131, 21), (68, 31), (34, 240), (20, 368), (10, 464)]
    (codeMat 204) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane456GenSource0106 :
    QuotientRankAtLeast (spanCodes [263, 133, 66, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 245), (133, 287), (66, 497), (36, 320), (20, 336), (10, 496)]
    (codeMat 214) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0107 :
    QuotientRankAtLeast (spanCodes [263, 134, 65, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(263, 176), (134, 480), (65, 320), (39, 436), (20, 507), (10, 437)]
    (codeMat 355) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0108 :
    QuotientRankAtLeast (spanCodes [260, 134, 66, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 16), (134, 176), (66, 480), (39, 506), (20, 436), (10, 507)]
    (codeMat 299) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane456GenSource0109 :
    QuotientRankAtLeast (spanCodes [288, 161, 66, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [280, 160, 84, 2, 1] [(288, 2), (161, 244), (66, 283), (20, 160), (10, 280)]
    (codeMat 86) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit146_lb15_wc

end QiushiMatmul
