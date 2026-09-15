import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit34Dispatch
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0160 :
    QuotientRankAtLeast (spanCodes [272, 144, 70, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(272, 261), (144, 260), (70, 10), (32, 320), (10, 160), (1, 16)]
    (codeMat 140) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane426GenSource0161 :
    QuotientRankAtLeast (spanCodes [262, 128, 96, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 261), (128, 260), (96, 430), (22, 356), (10, 475), (1, 192)]
    (codeMat 117) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane426GenSource0162 :
    QuotientRankAtLeast (spanCodes [262, 196, 36, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(262, 90), (196, 332), (36, 1), (22, 11), (10, 42), (1, 63)]
    (codeMat 467) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane426GenSource0163 :
    QuotientRankAtLeast (spanCodes [256, 160, 70, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (160, 69), (70, 160), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane426GenSource0164 :
    QuotientRankAtLeast (spanCodes [256, 162, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (162, 170), (68, 69), (16, 16), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane426GenSource0165 :
    QuotientRankAtLeast (spanCodes [262, 64, 34, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(262, 139), (64, 3), (34, 166), (22, 404), (10, 134), (1, 2)]
    (codeMat 141) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane426GenSource0166 :
    QuotientRankAtLeast (spanCodes [272, 146, 48, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 20, 8, 2, 1] [(272, 264), (146, 325), (48, 8), (10, 21), (6, 1), (1, 2)]
    (codeMat 401) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit34_lb14_unconditional

theorem plane426GenSource0167 :
    QuotientRankAtLeast (spanCodes [260, 134, 36, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 1), (134, 15), (36, 2), (20, 34), (10, 274), (1, 438)]
    (codeMat 157) (codeMat 95) (codeMat 244) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane426GenSource0168 :
    QuotientRankAtLeast (spanCodes [272, 146, 34, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(272, 306), (146, 438), (34, 34), (10, 15), (6, 2), (1, 1)]
    (codeMat 345) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane426GenSource0169 :
    QuotientRankAtLeast (spanCodes [272, 128, 50, 10, 4, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(272, 164), (128, 438), (50, 34), (10, 15), (4, 2), (1, 1)]
    (codeMat 409) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
