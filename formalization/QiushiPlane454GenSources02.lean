import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiStep128Mono346From214T
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 64, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 264), (64, 16), (32, 1), (20, 68), (10, 258)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane454GenSource0021 :
    QuotientRankAtLeast (spanCodes [289, 96, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(289, 434), (96, 310), (20, 43), (9, 32), (3, 1)]
    (codeMat 281) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane454GenSource0022 :
    QuotientRankAtLeast (spanCodes [291, 96, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(291, 392), (96, 164), (17, 11), (10, 10), (5, 32)]
    (codeMat 395) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane454GenSource0023 :
    QuotientRankAtLeast (spanCodes [257, 70, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(257, 175), (70, 353), (38, 38), (20, 20), (10, 51)]
    (codeMat 410) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane454GenSource0024 :
    QuotientRankAtLeast (spanCodes [260, 67, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(260, 32), (67, 507), (35, 464), (20, 341), (10, 506)]
    (codeMat 351) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane454GenSource0025 :
    QuotientRankAtLeast (spanCodes [290, 96, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 408), (96, 164), (17, 11), (10, 10), (5, 32)]
    (codeMat 395) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane454GenSource0026 :
    QuotientRankAtLeast (spanCodes [294, 166, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(294, 294), (166, 262), (96, 42), (20, 164), (10, 393)]
    (codeMat 230) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane454GenSource0027 :
    QuotientRankAtLeast (spanCodes [289, 160, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(289, 97), (160, 228), (96, 284), (20, 374), (10, 238)]
    (codeMat 431) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane454GenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 130, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(256, 1), (130, 256), (96, 10), (20, 97), (10, 276)]
    (codeMat 340) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane454GenSource0029 :
    QuotientRankAtLeast (spanCodes [390, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [424, 100, 16, 1] [(390, 1), (96, 424), (20, 101), (10, 476)]
    (codeMat 309) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit346_lb16_mono

end QiushiMatmul
