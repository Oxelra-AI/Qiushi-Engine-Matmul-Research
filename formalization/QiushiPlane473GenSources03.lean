import QiushiPlane473GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit214Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane473GenSource0030 :
    QuotientRankAtLeast (spanCodes [258, 147, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(258, 132), (147, 97), (84, 499), (39, 228), (10, 284)]
    (codeMat 111) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane473GenSource0031 :
    QuotientRankAtLeast (spanCodes [293, 162, 66, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(293, 505), (162, 132), (66, 284), (22, 402), (10, 228)]
    (codeMat 167) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane473GenSource0032 :
    QuotientRankAtLeast (spanCodes [293, 166, 70, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(293, 319), (166, 350), (70, 341), (18, 432), (10, 433)]
    (codeMat 482) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane473GenSource0033 :
    QuotientRankAtLeast (spanCodes [277, 133, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(277, 409), (133, 402), (84, 239), (48, 1), (10, 133)]
    (codeMat 114) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane473GenSource0034 :
    QuotientRankAtLeast (spanCodes [293, 167, 70, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(293, 475), (167, 442), (70, 341), (18, 1), (10, 433)]
    (codeMat 419) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane473GenSource0035 :
    QuotientRankAtLeast (spanCodes [288, 176, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(288, 1), (176, 10), (81, 374), (10, 228), (5, 504)]
    (codeMat 230) (codeMat 95) (codeMat 244) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane473GenSource0036 :
    QuotientRankAtLeast (spanCodes [257, 80, 32, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 20), (80, 96), (32, 1), (8, 8), (4, 2), (2, 128)]
    (codeMat 266) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane473GenSource0037 :
    QuotientRankAtLeast (spanCodes [257, 80, 32, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 22), (80, 252), (32, 3), (9, 9), (4, 2), (3, 130)]
    (codeMat 267) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane473GenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 80, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 150), (80, 232), (34, 22), (10, 30), (4, 2), (1, 3)]
    (codeMat 401) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane473GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 66, 39, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(258, 493), (66, 495), (39, 462), (22, 118), (10, 463)]
    (codeMat 419) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
