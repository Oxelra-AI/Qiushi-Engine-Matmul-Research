import QiushiPlane473GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane473GenSource0010 :
    QuotientRankAtLeast (spanCodes [293, 129, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(293, 506), (129, 33), (65, 1), (21, 350), (10, 43)]
    (codeMat 309) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane473GenSource0011 :
    QuotientRankAtLeast (spanCodes [293, 130, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(293, 506), (130, 32), (64, 1), (20, 373), (10, 43)]
    (codeMat 372) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane473GenSource0012 :
    QuotientRankAtLeast (spanCodes [291, 144, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(291, 97), (144, 1), (82, 21), (10, 31), (6, 256)]
    (codeMat 102) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane473GenSource0013 :
    QuotientRankAtLeast (spanCodes [293, 135, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(293, 383), (135, 132), (68, 164), (16, 1), (10, 11)]
    (codeMat 330) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane473GenSource0014 :
    QuotientRankAtLeast (spanCodes [260, 129, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(260, 1), (129, 97), (84, 474), (33, 326), (10, 430)]
    (codeMat 317) (codeMat 215) (codeMat 342) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane473GenSource0015 :
    QuotientRankAtLeast (spanCodes [258, 135, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 232), (135, 136), (84, 339), (39, 294), (10, 295)]
    (codeMat 355) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane473GenSource0016 :
    QuotientRankAtLeast (spanCodes [278, 147, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(278, 136), (147, 326), (84, 116), (51, 463), (10, 430)]
    (codeMat 415) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane473GenSource0017 :
    QuotientRankAtLeast (spanCodes [260, 128, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(260, 504), (128, 1), (84, 499), (33, 278), (10, 132)]
    (codeMat 212) (codeMat 355) (codeMat 190) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane473GenSource0018 :
    QuotientRankAtLeast (spanCodes [256, 132, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(256, 1), (132, 10), (84, 143), (37, 97), (10, 341)]
    (codeMat 396) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane473GenSource0019 :
    QuotientRankAtLeast (spanCodes [279, 147, 84, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(279, 107), (147, 278), (84, 375), (50, 133), (10, 132)]
    (codeMat 226) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
