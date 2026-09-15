import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit235Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0030 :
    QuotientRankAtLeast (spanCodes [259, 132, 84, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 136), (132, 96), (84, 116), (32, 1), (10, 262)]
    (codeMat 98) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane470GenSource0031 :
    QuotientRankAtLeast (spanCodes [259, 144, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 11), (144, 504), (84, 498), (52, 284), (10, 381)]
    (codeMat 461) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane470GenSource0032 :
    QuotientRankAtLeast (spanCodes [259, 161, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 136), (161, 339), (81, 373), (10, 463), (5, 1)]
    (codeMat 417) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470GenSource0033 :
    QuotientRankAtLeast (spanCodes [259, 163, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 505), (163, 239), (83, 381), (10, 97), (7, 1)]
    (codeMat 177) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane470GenSource0034 :
    QuotientRankAtLeast (spanCodes [259, 131, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 96), (131, 408), (84, 107), (38, 228), (10, 374)]
    (codeMat 110) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane470GenSource0035 :
    QuotientRankAtLeast (spanCodes [259, 135, 84, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 276), (135, 97), (84, 116), (34, 363), (10, 362)]
    (codeMat 426) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470GenSource0036 :
    QuotientRankAtLeast (spanCodes [259, 146, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 276), (146, 1), (84, 372), (55, 287), (10, 126)]
    (codeMat 431) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470GenSource0037 :
    QuotientRankAtLeast (spanCodes [259, 163, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 96), (163, 229), (82, 402), (10, 278), (6, 504)]
    (codeMat 302) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane470GenSource0038 :
    QuotientRankAtLeast (spanCodes [259, 131, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 97), (131, 96), (84, 157), (37, 411), (10, 232)]
    (codeMat 380) (codeMat 500) (codeMat 94) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane470GenSource0039 :
    QuotientRankAtLeast (spanCodes [259, 150, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 402), (150, 133), (84, 499), (48, 504), (10, 408)]
    (codeMat 95) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
