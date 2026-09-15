import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0260 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 139), (128, 9), (64, 1), (20, 252), (10, 31), (1, 3)]
    (codeMat 172) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0261 :
    QuotientRankAtLeast (spanCodes [256, 128, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 3), (128, 1), (69, 35), (19, 119), (10, 462)]
    (codeMat 428) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0262 :
    QuotientRankAtLeast (spanCodes [275, 144, 65, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(275, 171), (144, 128), (65, 32), (10, 294), (7, 1)]
    (codeMat 425) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane490GenSource0263 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 20), (129, 11), (65, 2), (21, 232), (9, 128), (3, 8)]
    (codeMat 205) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0264 :
    QuotientRankAtLeast (spanCodes [256, 160, 98, 19, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 256), (160, 164), (98, 212), (19, 446), (10, 463), (6, 16)]
    (codeMat 271) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane490GenSource0265 :
    QuotientRankAtLeast (spanCodes [256, 160, 97, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 256), (160, 196), (97, 180), (19, 463), (10, 446), (5, 16)]
    (codeMat 270) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane490GenSource0266 :
    QuotientRankAtLeast (spanCodes [258, 163, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 246), (163, 157), (96, 148), (17, 104), (10, 96), (5, 128)]
    (codeMat 94) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0267 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 20), (128, 9), (65, 2), (20, 96), (8, 128), (2, 8)]
    (codeMat 141) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0268 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (128, 9), (64, 1), (22, 255), (10, 31), (1, 3)]
    (codeMat 172) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0269 :
    QuotientRankAtLeast (spanCodes [274, 162, 114, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 149), (162, 150), (114, 117), (10, 105), (6, 1), (1, 8)]
    (codeMat 185) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
