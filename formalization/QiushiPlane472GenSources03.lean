import QiushiPlane472GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane472GenSource0030 :
    QuotientRankAtLeast (spanCodes [274, 149, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(274, 262), (149, 252), (84, 275), (48, 1), (10, 398)]
    (codeMat 482) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane472GenSource0031 :
    QuotientRankAtLeast (spanCodes [290, 160, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(290, 463), (160, 430), (81, 475), (10, 137), (5, 1)]
    (codeMat 345) (codeMat 470) (codeMat 213) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane472GenSource0032 :
    QuotientRankAtLeast (spanCodes [290, 162, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(290, 133), (162, 132), (83, 374), (10, 228), (7, 504)]
    (codeMat 188) (codeMat 461) (codeMat 234) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane472GenSource0033 :
    QuotientRankAtLeast (spanCodes [290, 163, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(290, 433), (163, 351), (82, 133), (10, 464), (6, 432)]
    (codeMat 215) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane472GenSource0034 :
    QuotientRankAtLeast (spanCodes [260, 128, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(260, 256), (128, 1), (84, 266), (38, 353), (10, 126)]
    (codeMat 372) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane472GenSource0035 :
    QuotientRankAtLeast (spanCodes [262, 130, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 11), (130, 1), (84, 143), (36, 32), (10, 507)]
    (codeMat 229) (codeMat 106) (codeMat 396) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane472GenSource0036 :
    QuotientRankAtLeast (spanCodes [263, 131, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(263, 441), (131, 238), (84, 311), (37, 316), (10, 349)]
    (codeMat 407) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane472GenSource0037 :
    QuotientRankAtLeast (spanCodes [279, 147, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(279, 233), (147, 306), (84, 443), (53, 21), (10, 20)]
    (codeMat 275) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane472GenSource0038 :
    QuotientRankAtLeast (spanCodes [275, 151, 84, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(275, 474), (151, 252), (84, 253), (49, 232), (10, 96)]
    (codeMat 157) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane472GenSource0039 :
    QuotientRankAtLeast (spanCodes [263, 130, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(263, 295), (130, 1), (84, 443), (37, 430), (10, 97)]
    (codeMat 405) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

end QiushiMatmul
