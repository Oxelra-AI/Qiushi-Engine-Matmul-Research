import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0080 :
    QuotientRankAtLeast (spanCodes [259, 162, 96, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 272), (162, 202), (96, 170), (18, 1), (10, 261), (6, 192)]
    (codeMat 99) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane457GenSource0081 :
    QuotientRankAtLeast (spanCodes [259, 162, 96, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 283), (162, 366), (96, 202), (16, 432), (10, 272), (4, 192)]
    (codeMat 95) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane457GenSource0082 :
    QuotientRankAtLeast (spanCodes [258, 163, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 246), (163, 157), (96, 148), (17, 104), (10, 96), (5, 128)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane457GenSource0083 :
    QuotientRankAtLeast (spanCodes [262, 166, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 464), (166, 170), (96, 202), (20, 191), (10, 475), (1, 192)]
    (codeMat 111) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane457GenSource0084 :
    QuotientRankAtLeast (spanCodes [256, 132, 69, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 256), (132, 452), (69, 257), (33, 97), (20, 479), (10, 430)]
    (codeMat 285) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane457GenSource0085 :
    QuotientRankAtLeast (spanCodes [261, 134, 66, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 367), (134, 453), (66, 464), (36, 1), (20, 261), (10, 96)]
    (codeMat 163) (codeMat 204) (codeMat 114) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane457GenSource0086 :
    QuotientRankAtLeast (spanCodes [288, 166, 70, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 320), (166, 347), (70, 11), (20, 437), (10, 78), (1, 1)]
    (codeMat 417) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane457GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (129, 160), (66, 176), (32, 1), (20, 78), (10, 436)]
    (codeMat 298) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane457GenSource0088 :
    QuotientRankAtLeast (spanCodes [260, 135, 66, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(260, 1), (135, 362), (66, 223), (38, 446), (20, 113), (10, 479)]
    (codeMat 405) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane457GenSource0089 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(260, 1), (129, 197), (68, 257), (38, 463), (20, 113), (10, 430)]
    (codeMat 277) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
