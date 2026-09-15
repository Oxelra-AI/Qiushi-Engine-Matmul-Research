import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0050 :
    QuotientRankAtLeast (spanCodes [289, 133, 101, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(289, 463), (133, 232), (101, 97), (20, 294), (10, 306)]
    (codeMat 214) (codeMat 501) (codeMat 494) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane457GenSource0051 :
    QuotientRankAtLeast (spanCodes [289, 134, 102, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(289, 20), (134, 96), (102, 156), (20, 97), (10, 398)]
    (codeMat 335) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane457GenSource0052 :
    QuotientRankAtLeast (spanCodes [289, 163, 67, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(289, 505), (163, 143), (67, 238), (20, 402), (10, 278)]
    (codeMat 158) (codeMat 382) (codeMat 499) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane457GenSource0053 :
    QuotientRankAtLeast (spanCodes [261, 196, 36, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(261, 362), (196, 21), (36, 1), (20, 257), (10, 97)]
    (codeMat 163) (codeMat 207) (codeMat 370) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane457GenSource0054 :
    QuotientRankAtLeast (spanCodes [288, 128, 97, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(288, 1), (128, 32), (97, 506), (20, 43), (10, 373)]
    (codeMat 318) (codeMat 93) (codeMat 372) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane457GenSource0055 :
    QuotientRankAtLeast (spanCodes [288, 133, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(288, 1), (133, 430), (100, 327), (20, 295), (10, 475)]
    (codeMat 190) (codeMat 214) (codeMat 214) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane457GenSource0056 :
    QuotientRankAtLeast (spanCodes [291, 134, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(291, 136), (134, 21), (100, 463), (20, 20), (10, 294)]
    (codeMat 143) (codeMat 107) (codeMat 428) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane457GenSource0057 :
    QuotientRankAtLeast (spanCodes [259, 194, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 97), (194, 373), (32, 1), (20, 11), (10, 30)]
    (codeMat 458) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane457GenSource0058 :
    QuotientRankAtLeast (spanCodes [258, 195, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 264), (195, 16), (32, 1), (20, 69), (10, 327)]
    (codeMat 106) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane457GenSource0059 :
    QuotientRankAtLeast (spanCodes [289, 224, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(289, 284), (224, 132), (16, 1), (10, 11), (4, 32)]
    (codeMat 266) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
