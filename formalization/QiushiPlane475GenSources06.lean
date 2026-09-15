import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0060 :
    QuotientRankAtLeast (spanCodes [256, 132, 65, 33, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 27), (132, 238), (65, 260), (33, 480), (17, 160), (10, 176)]
    (codeMat 159) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane475GenSource0061 :
    QuotientRankAtLeast (spanCodes [256, 135, 66, 34, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 27), (135, 378), (66, 462), (34, 479), (19, 446), (10, 463)]
    (codeMat 470) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane475GenSource0062 :
    QuotientRankAtLeast (spanCodes [260, 134, 67, 35, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 260), (134, 357), (67, 463), (35, 475), (22, 356), (10, 127)]
    (codeMat 230) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane475GenSource0063 :
    QuotientRankAtLeast (spanCodes [260, 130, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (130, 130), (71, 150), (39, 96), (17, 97), (10, 105)]
    (codeMat 107) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0064 :
    QuotientRankAtLeast (spanCodes [263, 131, 70, 38, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 170), (131, 378), (70, 191), (38, 160), (18, 432), (10, 180)]
    (codeMat 143) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane475GenSource0065 :
    QuotientRankAtLeast (spanCodes [262, 134, 67, 35, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 160), (134, 176), (67, 480), (35, 78), (22, 436), (10, 507)]
    (codeMat 355) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane475GenSource0066 :
    QuotientRankAtLeast (spanCodes [293, 165, 96, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(293, 430), (165, 431), (96, 437), (21, 480), (9, 320), (3, 16)]
    (codeMat 204) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane475GenSource0067 :
    QuotientRankAtLeast (spanCodes [258, 132, 65, 33, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 148), (132, 150), (65, 130), (33, 252), (23, 255), (10, 227)]
    (codeMat 110) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0068 :
    QuotientRankAtLeast (spanCodes [259, 146, 82, 50, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 272), (146, 1), (82, 433), (50, 31), (10, 223), (5, 260)]
    (codeMat 111) (codeMat 107) (codeMat 428) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane475GenSource0069 :
    QuotientRankAtLeast (spanCodes [291, 163, 96, 17, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(291, 118), (163, 244), (96, 245), (17, 96), (10, 104), (6, 128)]
    (codeMat 93) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
