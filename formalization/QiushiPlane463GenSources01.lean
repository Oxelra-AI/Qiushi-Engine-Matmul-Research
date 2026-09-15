import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0010 :
    QuotientRankAtLeast (spanCodes [134, 68, 32, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(134, 164), (68, 475), (32, 32), (21, 11), (10, 42)]
    (codeMat 339) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0011 :
    QuotientRankAtLeast (spanCodes [133, 68, 32, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(133, 350), (68, 497), (32, 1), (22, 33), (10, 42)]
    (codeMat 474) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0012 :
    QuotientRankAtLeast (spanCodes [133, 68, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(133, 164), (68, 475), (34, 10), (20, 11), (10, 42)]
    (codeMat 275) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0013 :
    QuotientRankAtLeast (spanCodes [132, 68, 33, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 496), (68, 497), (33, 175), (22, 464), (10, 42)]
    (codeMat 468) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0014 :
    QuotientRankAtLeast (spanCodes [132, 68, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 507), (68, 475), (35, 341), (20, 506), (10, 42)]
    (codeMat 286) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0015 :
    QuotientRankAtLeast (spanCodes [256, 178, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(256, 16), (178, 343), (68, 10), (10, 79), (1, 1)]
    (codeMat 417) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane463GenSource0016 :
    QuotientRankAtLeast (spanCodes [258, 178, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 327), (178, 343), (68, 69), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane463GenSource0017 :
    QuotientRankAtLeast (spanCodes [260, 167, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(260, 1), (167, 443), (68, 433), (20, 97), (10, 341)]
    (codeMat 405) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane463GenSource0018 :
    QuotientRankAtLeast (spanCodes [260, 166, 68, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(260, 432), (166, 238), (68, 433), (21, 97), (10, 341)]
    (codeMat 468) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane463GenSource0019 :
    QuotientRankAtLeast (spanCodes [261, 164, 68, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(261, 319), (164, 238), (68, 228), (23, 97), (10, 341)]
    (codeMat 342) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

end QiushiMatmul
