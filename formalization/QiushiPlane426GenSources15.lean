import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0150 :
    QuotientRankAtLeast (spanCodes [272, 148, 68, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(272, 378), (148, 453), (68, 164), (36, 16), (10, 96), (1, 256)]
    (codeMat 95) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane426GenSource0151 :
    QuotientRankAtLeast (spanCodes [272, 150, 70, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(272, 437), (150, 430), (70, 26), (36, 320), (10, 160), (1, 16)]
    (codeMat 204) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane426GenSource0152 :
    QuotientRankAtLeast (spanCodes [272, 150, 68, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(272, 222), (150, 197), (68, 164), (38, 368), (10, 96), (1, 256)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane426GenSource0153 :
    QuotientRankAtLeast (spanCodes [272, 144, 68, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(272, 26), (144, 1), (68, 164), (32, 16), (10, 96), (1, 256)]
    (codeMat 86) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane426GenSource0154 :
    QuotientRankAtLeast (spanCodes [256, 132, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 16), (132, 160), (96, 170), (16, 260), (10, 69), (1, 320)]
    (codeMat 99) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane426GenSource0155 :
    QuotientRankAtLeast (spanCodes [256, 162, 70, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (162, 245), (70, 176), (16, 27), (10, 10), (1, 16)]
    (codeMat 267) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane426GenSource0156 :
    QuotientRankAtLeast (spanCodes [272, 146, 82, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(272, 112), (146, 1), (82, 33), (54, 63), (10, 265), (1, 365)]
    (codeMat 167) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane426GenSource0157 :
    QuotientRankAtLeast (spanCodes [272, 134, 68, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(272, 21), (134, 30), (68, 366), (52, 20), (10, 160), (1, 432)]
    (codeMat 215) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane426GenSource0158 :
    QuotientRankAtLeast (spanCodes [272, 150, 82, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(272, 127), (150, 255), (82, 235), (50, 356), (10, 357), (1, 260)]
    (codeMat 106) (codeMat 247) (codeMat 379) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane426GenSource0159 :
    QuotientRankAtLeast (spanCodes [272, 128, 70, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(272, 321), (128, 260), (70, 170), (48, 320), (10, 160), (1, 16)]
    (codeMat 142) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
