import QiushiPlane469GenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane469GenSource0040 :
    QuotientRankAtLeast (spanCodes [258, 135, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(258, 263), (135, 252), (84, 157), (51, 506), (10, 495)]
    (codeMat 351) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane469GenSource0041 :
    QuotientRankAtLeast (spanCodes [258, 147, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(258, 132), (147, 97), (84, 499), (39, 228), (10, 284)]
    (codeMat 111) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane469GenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 148, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 295), (148, 475), (84, 474), (33, 430), (10, 97)]
    (codeMat 412) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0043 :
    QuotientRankAtLeast (spanCodes [258, 160, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 97), (160, 430), (65, 1), (21, 475), (10, 295)]
    (codeMat 125) (codeMat 407) (codeMat 405) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0044 :
    QuotientRankAtLeast (spanCodes [258, 133, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(258, 232), (133, 411), (84, 157), (51, 507), (10, 263)]
    (codeMat 247) (codeMat 225) (codeMat 169) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane469GenSource0045 :
    QuotientRankAtLeast (spanCodes [258, 145, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(258, 132), (145, 374), (84, 499), (39, 96), (10, 408)]
    (codeMat 85) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane469GenSource0046 :
    QuotientRankAtLeast (spanCodes [258, 151, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 295), (151, 338), (84, 339), (33, 430), (10, 463)]
    (codeMat 405) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0047 :
    QuotientRankAtLeast (spanCodes [258, 167, 69, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(258, 466), (167, 142), (69, 228), (17, 11), (10, 10)]
    (codeMat 275) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane469GenSource0048 :
    QuotientRankAtLeast (spanCodes [258, 176, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 33), (176, 42), (82, 350), (10, 497), (6, 1)]
    (codeMat 369) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane469GenSource0049 :
    QuotientRankAtLeast (spanCodes [258, 178, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(258, 352), (178, 353), (80, 21), (10, 383), (4, 256)]
    (codeMat 102) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
