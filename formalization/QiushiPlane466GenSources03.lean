import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit166Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit235Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0030 :
    QuotientRankAtLeast (spanCodes [278, 132, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(278, 387), (132, 424), (68, 392), (39, 294), (10, 295)]
    (codeMat 355) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane466GenSource0031 :
    QuotientRankAtLeast (spanCodes [257, 147, 68, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(257, 284), (147, 175), (68, 316), (48, 1), (10, 441)]
    (codeMat 370) (codeMat 501) (codeMat 494) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane466GenSource0032 :
    QuotientRankAtLeast (spanCodes [263, 149, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(263, 418), (149, 424), (68, 175), (54, 1), (10, 295)]
    (codeMat 443) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane466GenSource0033 :
    QuotientRankAtLeast (spanCodes [279, 130, 68, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(279, 443), (130, 1), (68, 462), (38, 20), (10, 294)]
    (codeMat 157) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane466GenSource0034 :
    QuotientRankAtLeast (spanCodes [277, 129, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(277, 142), (129, 175), (68, 441), (36, 1), (10, 133)]
    (codeMat 179) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane466GenSource0035 :
    QuotientRankAtLeast (spanCodes [272, 132, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(272, 352), (132, 136), (68, 137), (33, 475), (10, 508)]
    (codeMat 172) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane466GenSource0036 :
    QuotientRankAtLeast (spanCodes [263, 147, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(263, 349), (147, 343), (68, 316), (54, 1), (10, 322)]
    (codeMat 171) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane466GenSource0037 :
    QuotientRankAtLeast (spanCodes [257, 149, 68, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(257, 78), (149, 332), (68, 79), (48, 16), (10, 280)]
    (codeMat 213) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane466GenSource0038 :
    QuotientRankAtLeast (spanCodes [259, 148, 68, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 136), (148, 252), (68, 232), (50, 295), (10, 294)]
    (codeMat 354) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane466GenSource0039 :
    QuotientRankAtLeast (spanCodes [278, 128, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(278, 349), (128, 27), (68, 343), (39, 264), (10, 280)]
    (codeMat 159) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

end QiushiMatmul
