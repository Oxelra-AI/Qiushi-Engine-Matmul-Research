import QiushiPlane463LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit351From217
import QiushiStep99Orbit150Dispatch
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463LowerGenSource0010 :
    QuotientRankAtLeast (spanCodes [135, 68, 33, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(135, 507), (68, 475), (33, 383), (21, 506), (10, 42)]
    (codeMat 351) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0011 :
    QuotientRankAtLeast (spanCodes [135, 68, 35, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(135, 496), (68, 497), (35, 133), (23, 464), (10, 42)]
    (codeMat 405) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0012 :
    QuotientRankAtLeast (spanCodes [134, 68, 32, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(134, 164), (68, 475), (32, 32), (21, 11), (10, 42)]
    (codeMat 339) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0013 :
    QuotientRankAtLeast (spanCodes [134, 68, 34, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(134, 350), (68, 497), (34, 43), (23, 33), (10, 42)]
    (codeMat 410) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0014 :
    QuotientRankAtLeast (spanCodes [133, 68, 32, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(133, 350), (68, 497), (32, 1), (22, 33), (10, 42)]
    (codeMat 474) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0015 :
    QuotientRankAtLeast (spanCodes [132, 68, 33, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 496), (68, 497), (33, 175), (22, 464), (10, 42)]
    (codeMat 468) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463LowerGenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 178, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(256, 16), (178, 343), (68, 10), (10, 79), (1, 1)]
    (codeMat 417) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane463LowerGenSource0017 :
    QuotientRankAtLeast (spanCodes [258, 178, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 327), (178, 343), (68, 69), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane463LowerGenSource0018 :
    QuotientRankAtLeast (spanCodes [260, 179, 68, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [302, 228, 16, 1] [(260, 1), (179, 318), (68, 17), (10, 245)]
    (codeMat 421) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit351_lb16_mono

theorem plane463LowerGenSource0019 :
    QuotientRankAtLeast (spanCodes [261, 179, 68, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [302, 228, 16, 1] [(261, 319), (179, 318), (68, 228), (10, 245)]
    (codeMat 311) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit351_lb16_mono

end QiushiMatmul
