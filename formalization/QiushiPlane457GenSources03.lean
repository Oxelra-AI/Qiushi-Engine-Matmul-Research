import QiushiPlane457GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane457GenSource0030 :
    QuotientRankAtLeast (spanCodes [322, 131, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(322, 97), (131, 373), (39, 31), (20, 21), (10, 30)]
    (codeMat 395) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane457GenSource0031 :
    QuotientRankAtLeast (spanCodes [353, 160, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(353, 308), (160, 68), (16, 1), (10, 78), (4, 288)]
    (codeMat 298) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane457GenSource0032 :
    QuotientRankAtLeast (spanCodes [352, 161, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(352, 363), (161, 277), (17, 96), (10, 352), (5, 1)]
    (codeMat 249) (codeMat 380) (codeMat 117) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane457GenSource0033 :
    QuotientRankAtLeast (spanCodes [323, 130, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(323, 264), (130, 16), (39, 326), (20, 258), (10, 327)]
    (codeMat 107) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane457GenSource0034 :
    QuotientRankAtLeast (spanCodes [326, 135, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(326, 301), (135, 164), (34, 10), (20, 11), (10, 42)]
    (codeMat 339) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane457GenSource0035 :
    QuotientRankAtLeast (spanCodes [353, 160, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(353, 263), (160, 175), (17, 10), (10, 11), (5, 32)]
    (codeMat 331) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane457GenSource0036 :
    QuotientRankAtLeast (spanCodes [352, 161, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(352, 435), (161, 143), (19, 310), (10, 402), (7, 32)]
    (codeMat 95) (codeMat 379) (codeMat 247) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane457GenSource0037 :
    QuotientRankAtLeast (spanCodes [320, 129, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(320, 1), (129, 441), (38, 164), (20, 402), (10, 278)]
    (codeMat 156) (codeMat 382) (codeMat 499) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane457GenSource0038 :
    QuotientRankAtLeast (spanCodes [324, 133, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(324, 362), (133, 21), (34, 96), (20, 352), (10, 97)]
    (codeMat 226) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane457GenSource0039 :
    QuotientRankAtLeast (spanCodes [355, 162, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(355, 311), (162, 175), (17, 10), (10, 11), (5, 32)]
    (codeMat 267) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
