import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiOrbit35FP
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0070 :
    QuotientRankAtLeast (spanCodes [384, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(384, 3), (64, 1), (20, 368), (10, 104), (1, 8)]
    (codeMat 140) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane457GenSource0071 :
    QuotientRankAtLeast (spanCodes [384, 65, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(384, 128), (65, 1), (16, 32), (10, 268), (4, 390)]
    (codeMat 277) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane457GenSource0072 :
    QuotientRankAtLeast (spanCodes [419, 98, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(419, 395), (98, 426), (18, 384), (10, 127), (6, 1)]
    (codeMat 369) (codeMat 397) (codeMat 250) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane457GenSource0073 :
    QuotientRankAtLeast (spanCodes [325, 132, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(325, 9), (132, 274), (39, 368), (20, 272), (10, 376)]
    (codeMat 94) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane457GenSource0074 :
    QuotientRankAtLeast (spanCodes [352, 161, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(352, 469), (161, 117), (18, 1), (10, 510), (6, 384)]
    (codeMat 355) (codeMat 334) (codeMat 442) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane457GenSource0075 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 20), (128, 1), (64, 2), (20, 96), (8, 128), (2, 8)]
    (codeMat 140) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane457GenSource0076 :
    QuotientRankAtLeast (spanCodes [256, 165, 100, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 27), (165, 174), (100, 10), (20, 368), (9, 16), (3, 256)]
    (codeMat 95) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane457GenSource0077 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 22), (128, 3), (64, 2), (20, 232), (9, 128), (3, 8)]
    (codeMat 204) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane457GenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 139), (130, 9), (64, 2), (20, 252), (10, 31), (1, 3)]
    (codeMat 165) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane457GenSource0079 :
    QuotientRankAtLeast (spanCodes [256, 161, 96, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 432), (161, 106), (96, 462), (17, 475), (10, 283), (5, 260)]
    (codeMat 110) (codeMat 443) (codeMat 254) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
