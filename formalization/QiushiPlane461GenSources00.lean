import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit347From150
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit300Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0000 :
    QuotientRankAtLeast (spanCodes [162, 68, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 10, 1] [(162, 228), (68, 11), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit300_lb17_wc

theorem plane461GenSource0001 :
    QuotientRankAtLeast (spanCodes [263, 133, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(263, 464), (133, 133), (68, 42), (39, 496), (10, 497)]
    (codeMat 419) (codeMat 171) (codeMat 485) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane461GenSource0002 :
    QuotientRankAtLeast (spanCodes [279, 149, 68, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(279, 143), (149, 43), (68, 475), (55, 175), (10, 497)]
    (codeMat 375) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane461GenSource0003 :
    QuotientRankAtLeast (spanCodes [279, 148, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(279, 382), (148, 133), (68, 475), (54, 1), (10, 497)]
    (codeMat 379) (codeMat 395) (codeMat 474) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane461GenSource0004 :
    QuotientRankAtLeast (spanCodes [263, 135, 68, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(263, 11), (135, 43), (68, 42), (37, 175), (10, 497)]
    (codeMat 485) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane461GenSource0005 :
    QuotientRankAtLeast (spanCodes [279, 151, 68, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(279, 165), (151, 133), (68, 475), (53, 496), (10, 497)]
    (codeMat 307) (codeMat 431) (codeMat 477) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane461GenSource0006 :
    QuotientRankAtLeast (spanCodes [263, 134, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(263, 506), (134, 133), (68, 42), (36, 1), (10, 497)]
    (codeMat 491) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane461GenSource0007 :
    QuotientRankAtLeast (spanCodes [292, 162, 68, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(292, 16), (162, 17), (68, 258), (10, 245)]
    (codeMat 317) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane461GenSource0008 :
    QuotientRankAtLeast (spanCodes [279, 133, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(279, 157), (133, 20), (68, 294), (39, 463), (10, 462)]
    (codeMat 355) (codeMat 382) (codeMat 499) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane461GenSource0009 :
    QuotientRankAtLeast (spanCodes [262, 131, 68, 33, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 440), (131, 240), (68, 280), (33, 263), (23, 262), (10, 323)]
    (codeMat 107) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

end QiushiMatmul
