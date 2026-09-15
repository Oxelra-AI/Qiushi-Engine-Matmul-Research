import QiushiPlane469GenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane469GenSource0030 :
    QuotientRankAtLeast (spanCodes [258, 129, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 97), (129, 430), (84, 474), (48, 1), (10, 326)]
    (codeMat 234) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0031 :
    QuotientRankAtLeast (spanCodes [258, 144, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 295), (144, 1), (84, 474), (33, 430), (10, 326)]
    (codeMat 318) (codeMat 359) (codeMat 174) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0032 :
    QuotientRankAtLeast (spanCodes [258, 148, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 462), (148, 306), (84, 307), (37, 232), (10, 326)]
    (codeMat 500) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0033 :
    QuotientRankAtLeast (spanCodes [258, 149, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 136), (149, 475), (84, 307), (36, 1), (10, 326)]
    (codeMat 107) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0034 :
    QuotientRankAtLeast (spanCodes [258, 166, 67, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 338), (166, 475), (67, 327), (23, 232), (10, 326)]
    (codeMat 423) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0035 :
    QuotientRankAtLeast (spanCodes [258, 129, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 463), (129, 430), (84, 339), (51, 96), (10, 232)]
    (codeMat 206) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0036 :
    QuotientRankAtLeast (spanCodes [258, 133, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(258, 408), (133, 374), (84, 499), (55, 278), (10, 132)]
    (codeMat 159) (codeMat 225) (codeMat 169) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane469GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 135, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(258, 284), (135, 97), (84, 499), (53, 133), (10, 132)]
    (codeMat 163) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane469GenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 147, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 295), (147, 136), (84, 339), (33, 430), (10, 232)]
    (codeMat 382) (codeMat 444) (codeMat 110) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane469GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 166, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(258, 31), (166, 11), (64, 256), (20, 21), (10, 383)]
    (codeMat 286) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
