import QiushiPlane476GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane476GenSource0030 :
    QuotientRankAtLeast (spanCodes [276, 147, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(276, 284), (147, 408), (84, 285), (52, 228), (10, 374)]
    (codeMat 124) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane476GenSource0031 :
    QuotientRankAtLeast (spanCodes [276, 148, 83, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(276, 399), (148, 398), (83, 411), (51, 96), (10, 232)]
    (codeMat 204) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane476GenSource0032 :
    QuotientRankAtLeast (spanCodes [276, 129, 81, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(276, 43), (129, 133), (81, 42), (49, 475), (10, 383)]
    (codeMat 125) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane476GenSource0033 :
    QuotientRankAtLeast (spanCodes [276, 151, 70, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(276, 462), (151, 136), (70, 430), (38, 252), (10, 295)]
    (codeMat 247) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane476GenSource0034 :
    QuotientRankAtLeast (spanCodes [276, 145, 69, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(276, 232), (145, 252), (69, 21), (37, 338), (10, 475)]
    (codeMat 172) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane476GenSource0035 :
    QuotientRankAtLeast (spanCodes [276, 149, 65, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(276, 381), (149, 132), (65, 504), (33, 408), (10, 238)]
    (codeMat 444) (codeMat 234) (codeMat 461) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane476GenSource0036 :
    QuotientRankAtLeast (spanCodes [276, 150, 64, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(276, 10), (150, 21), (64, 256), (32, 1), (10, 127)]
    (codeMat 314) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane476GenSource0037 :
    QuotientRankAtLeast (spanCodes [259, 132, 69, 37, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(259, 440), (132, 488), (69, 280), (37, 263), (23, 69), (10, 323)]
    (codeMat 98) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane476GenSource0038 :
    QuotientRankAtLeast (spanCodes [260, 166, 96, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(260, 1), (166, 11), (96, 434), (16, 32), (10, 284)]
    (codeMat 181) (codeMat 93) (codeMat 372) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane476GenSource0039 :
    QuotientRankAtLeast (spanCodes [276, 181, 96, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(276, 374), (181, 239), (96, 284), (9, 504), (3, 1)]
    (codeMat 369) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
