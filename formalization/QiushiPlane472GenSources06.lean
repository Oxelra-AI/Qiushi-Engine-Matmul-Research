import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit128Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0060 :
    QuotientRankAtLeast (spanCodes [290, 165, 70, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(290, 97), (165, 442), (70, 228), (18, 1), (10, 433)]
    (codeMat 307) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane472GenSource0061 :
    QuotientRankAtLeast (spanCodes [290, 166, 69, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(290, 278), (166, 132), (69, 228), (17, 11), (10, 10)]
    (codeMat 339) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane472GenSource0062 :
    QuotientRankAtLeast (spanCodes [290, 65, 18, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(290, 399), (65, 192), (18, 1), (10, 17), (7, 36)]
    (codeMat 339) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane472GenSource0063 :
    QuotientRankAtLeast (spanCodes [290, 67, 18, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(290, 43), (67, 294), (18, 390), (10, 262), (5, 1)]
    (codeMat 185) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane472GenSource0064 :
    QuotientRankAtLeast (spanCodes [257, 80, 32, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 22), (80, 252), (32, 3), (9, 9), (4, 2), (3, 130)]
    (codeMat 267) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0065 :
    QuotientRankAtLeast (spanCodes [256, 80, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 128), (80, 224), (34, 20), (10, 28), (4, 2), (1, 3)]
    (codeMat 273) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane472GenSource0066 :
    QuotientRankAtLeast (spanCodes [262, 64, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(262, 269), (64, 390), (36, 32), (20, 33), (10, 43)]
    (codeMat 410) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane472GenSource0067 :
    QuotientRankAtLeast (spanCodes [260, 64, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(260, 192), (64, 16), (38, 427), (20, 245), (10, 378)]
    (codeMat 358) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane472GenSource0068 :
    QuotientRankAtLeast (spanCodes [261, 64, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(261, 386), (64, 384), (39, 97), (20, 108), (10, 96)]
    (codeMat 107) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane472GenSource0069 :
    QuotientRankAtLeast (spanCodes [273, 84, 49, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(273, 500), (84, 116), (49, 11), (8, 1), (2, 32)]
    (codeMat 330) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

end QiushiMatmul
