import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0070 :
    QuotientRankAtLeast (spanCodes [293, 132, 99, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(293, 508), (132, 353), (99, 339), (20, 352), (10, 136)]
    (codeMat 158) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane458GenSource0071 :
    QuotientRankAtLeast (spanCodes [293, 135, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(293, 440), (135, 316), (96, 408), (20, 133), (10, 175)]
    (codeMat 351) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane458GenSource0072 :
    QuotientRankAtLeast (spanCodes [289, 227, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(289, 316), (227, 132), (16, 1), (10, 11), (4, 32)]
    (codeMat 330) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane458GenSource0073 :
    QuotientRankAtLeast (spanCodes [450, 35, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(450, 170), (35, 11), (18, 63), (10, 62), (6, 32)]
    (codeMat 458) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane458GenSource0074 :
    QuotientRankAtLeast (spanCodes [449, 33, 16, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(449, 120), (33, 60), (16, 2), (9, 63), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane458GenSource0075 :
    QuotientRankAtLeast (spanCodes [450, 32, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(450, 112), (32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane458GenSource0076 :
    QuotientRankAtLeast (spanCodes [387, 65, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(387, 11), (65, 32), (18, 390), (10, 262), (6, 1)]
    (codeMat 169) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane458GenSource0077 :
    QuotientRankAtLeast (spanCodes [385, 67, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(385, 126), (67, 469), (36, 32), (20, 33), (10, 42)]
    (codeMat 410) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane458GenSource0078 :
    QuotientRankAtLeast (spanCodes [323, 129, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(323, 300), (129, 138), (17, 10), (10, 11), (5, 32)]
    (codeMat 395) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane458GenSource0079 :
    QuotientRankAtLeast (spanCodes [323, 129, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(323, 422), (129, 138), (18, 1), (10, 129), (6, 390)]
    (codeMat 171) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
