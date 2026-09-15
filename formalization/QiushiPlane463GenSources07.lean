import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit108From29
import QiushiOrbit29FP
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0070 :
    QuotientRankAtLeast (spanCodes [290, 164, 68, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(290, 20), (164, 21), (68, 462), (23, 430), (10, 232)]
    (codeMat 445) (codeMat 124) (codeMat 124) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane463GenSource0071 :
    QuotientRankAtLeast (spanCodes [272, 149, 68, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(272, 228), (149, 133), (68, 373), (38, 287), (10, 497)]
    (codeMat 431) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane463GenSource0072 :
    QuotientRankAtLeast (spanCodes [288, 165, 68, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(288, 1), (165, 253), (68, 462), (22, 96), (10, 232)]
    (codeMat 158) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane463GenSource0073 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 96), (130, 256), (68, 353), (49, 21), (10, 383)]
    (codeMat 348) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0074 :
    QuotientRankAtLeast (spanCodes [263, 131, 68, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(263, 10), (131, 21), (68, 30), (48, 256), (10, 383)]
    (codeMat 172) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0075 :
    QuotientRankAtLeast (spanCodes [272, 148, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 238), (148, 374), (68, 96), (39, 133), (10, 132)]
    (codeMat 107) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0076 :
    QuotientRankAtLeast (spanCodes [274, 150, 68, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(274, 381), (150, 97), (68, 228), (37, 402), (10, 132)]
    (codeMat 94) (codeMat 486) (codeMat 157) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0077 :
    QuotientRankAtLeast (spanCodes [161, 68, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(161, 84), (68, 160), (16, 1), (8, 2), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

theorem plane463GenSource0078 :
    QuotientRankAtLeast (spanCodes [161, 68, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 8, 2, 1] [(161, 244), (68, 160), (17, 11), (9, 2), (3, 8)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit108_lb15_mono

theorem plane463GenSource0079 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
