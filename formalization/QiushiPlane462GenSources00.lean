import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit377Dispatch
import QiushiWcOrbit204Dispatch
import QiushiWcOrbit216Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0000 :
    QuotientRankAtLeast (spanCodes [161, 68, 19, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 68, 19, 10] [(161, 87), (68, 184), (19, 25), (10, 10)]
    (codeMat 266) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit377_lb17_unconditional

theorem plane462GenSource0001 :
    QuotientRankAtLeast (spanCodes [262, 163, 68, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(262, 176), (163, 486), (68, 424), (17, 68), (10, 69)]
    (codeMat 99) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane462GenSource0002 :
    QuotientRankAtLeast (spanCodes [263, 162, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(263, 176), (162, 78), (68, 424), (16, 1), (10, 69)]
    (codeMat 98) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane462GenSource0003 :
    QuotientRankAtLeast (spanCodes [278, 178, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(278, 343), (178, 493), (68, 10), (10, 69), (1, 1)]
    (codeMat 161) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane462GenSource0004 :
    QuotientRankAtLeast (spanCodes [277, 131, 68, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(277, 419), (131, 424), (68, 456), (49, 418), (10, 238)]
    (codeMat 303) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane462GenSource0005 :
    QuotientRankAtLeast (spanCodes [263, 133, 68, 38, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(263, 440), (133, 160), (68, 488), (38, 263), (17, 68), (10, 69)]
    (codeMat 99) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0006 :
    QuotientRankAtLeast (spanCodes [263, 133, 68, 33, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(263, 191), (133, 91), (68, 502), (33, 440), (22, 280), (10, 240)]
    (codeMat 86) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0007 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 33, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 68), (134, 69), (68, 262), (33, 160), (21, 488), (10, 240)]
    (codeMat 92) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0008 :
    QuotientRankAtLeast (spanCodes [263, 134, 68, 37, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(263, 80), (134, 160), (68, 488), (37, 322), (17, 68), (10, 69)]
    (codeMat 107) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0009 :
    QuotientRankAtLeast (spanCodes [263, 129, 68, 38, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(263, 322), (129, 323), (68, 262), (38, 80), (21, 280), (10, 240)]
    (codeMat 85) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

end QiushiMatmul
