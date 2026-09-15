import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0090 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (64, 128), (32, 3), (20, 28), (10, 224)]
    (codeMat 102) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane454GenSource0091 :
    QuotientRankAtLeast (spanCodes [258, 163, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 246), (163, 157), (96, 148), (17, 104), (10, 96), (5, 128)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane454GenSource0092 :
    QuotientRankAtLeast (spanCodes [259, 160, 96, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(259, 11), (160, 196), (96, 197), (19, 463), (10, 446), (7, 16)]
    (codeMat 396) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane454GenSource0093 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 452), (129, 257), (65, 256), (33, 479), (20, 430), (10, 97)]
    (codeMat 348) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane454GenSource0094 :
    QuotientRankAtLeast (spanCodes [257, 135, 67, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(257, 507), (135, 255), (67, 31), (35, 368), (20, 245), (10, 30)]
    (codeMat 375) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane454GenSource0095 :
    QuotientRankAtLeast (spanCodes [261, 131, 67, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 420), (131, 160), (67, 272), (35, 367), (20, 170), (10, 464)]
    (codeMat 334) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane454GenSource0096 :
    QuotientRankAtLeast (spanCodes [290, 130, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(290, 463), (130, 1), (96, 469), (17, 96), (10, 352), (5, 16)]
    (codeMat 205) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane454GenSource0097 :
    QuotientRankAtLeast (spanCodes [263, 128, 65, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(263, 191), (128, 27), (65, 256), (33, 97), (20, 430), (10, 479)]
    (codeMat 351) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane454GenSource0098 :
    QuotientRankAtLeast (spanCodes [386, 67, 35, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(386, 112), (67, 344), (35, 31), (19, 30), (10, 53), (7, 32)]
    (codeMat 266) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane454GenSource0099 :
    QuotientRankAtLeast (spanCodes [260, 161, 96, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 1), (161, 443), (96, 453), (20, 20), (9, 260), (3, 432)]
    (codeMat 213) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
