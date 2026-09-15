import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0070 :
    QuotientRankAtLeast (spanCodes [292, 162, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(292, 260), (162, 68), (68, 176), (16, 1), (10, 10), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane461GenSource0071 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(262, 297), (132, 101), (68, 90), (38, 296), (22, 264), (10, 376)]
    (codeMat 214) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane461GenSource0072 :
    QuotientRankAtLeast (spanCodes [288, 160, 68, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(288, 1), (160, 33), (68, 113), (20, 100), (8, 63), (2, 365)]
    (codeMat 230) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane461GenSource0073 :
    QuotientRankAtLeast (spanCodes [263, 133, 68, 39, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 21), (133, 464), (68, 367), (39, 20), (23, 272), (10, 420)]
    (codeMat 142) (codeMat 205) (codeMat 242) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane461GenSource0074 :
    QuotientRankAtLeast (spanCodes [263, 132, 68, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 433), (132, 223), (68, 367), (38, 283), (22, 475), (10, 420)]
    (codeMat 181) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane461GenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 32, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 193), (130, 192), (68, 203), (32, 260), (21, 272), (10, 420)]
    (codeMat 140) (codeMat 461) (codeMat 234) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane461GenSource0076 :
    QuotientRankAtLeast (spanCodes [259, 130, 68, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 430), (130, 260), (68, 203), (32, 192), (20, 475), (10, 420)]
    (codeMat 167) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane461GenSource0077 :
    QuotientRankAtLeast (spanCodes [259, 133, 68, 39, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 353), (133, 378), (68, 180), (39, 97), (19, 446), (10, 113)]
    (codeMat 478) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane461GenSource0078 :
    QuotientRankAtLeast (spanCodes [256, 147, 66, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 432), (147, 261), (66, 96), (49, 283), (10, 356), (6, 192)]
    (codeMat 111) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane461GenSource0079 :
    QuotientRankAtLeast (spanCodes [275, 131, 65, 33, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(275, 270), (131, 283), (65, 192), (33, 261), (10, 356), (5, 260)]
    (codeMat 115) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
