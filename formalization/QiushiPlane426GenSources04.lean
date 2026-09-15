import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0040 :
    QuotientRankAtLeast (spanCodes [272, 162, 118, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(272, 175), (162, 133), (118, 434), (10, 316), (1, 32)]
    (codeMat 335) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane426GenSource0041 :
    QuotientRankAtLeast (spanCodes [272, 182, 98, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(272, 316), (182, 228), (98, 106), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane426GenSource0042 :
    QuotientRankAtLeast (spanCodes [272, 132, 82, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(272, 373), (132, 97), (82, 21), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane426GenSource0043 :
    QuotientRankAtLeast (spanCodes [272, 162, 116, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(272, 175), (162, 441), (116, 311), (10, 316), (1, 32)]
    (codeMat 117) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane426GenSource0044 :
    QuotientRankAtLeast (spanCodes [272, 176, 102, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(272, 319), (176, 228), (102, 106), (10, 10), (1, 1)]
    (codeMat 409) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane426GenSource0045 :
    QuotientRankAtLeast (spanCodes [272, 178, 100, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 374), (178, 238), (100, 97), (10, 10), (1, 1)]
    (codeMat 409) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane426GenSource0046 :
    QuotientRankAtLeast (spanCodes [272, 180, 98, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 402), (180, 228), (98, 143), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane426GenSource0047 :
    QuotientRankAtLeast (spanCodes [272, 146, 116, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(272, 393), (146, 1), (116, 142), (10, 300), (1, 32)]
    (codeMat 271) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane426GenSource0048 :
    QuotientRankAtLeast (spanCodes [272, 148, 114, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(272, 435), (148, 43), (114, 142), (10, 316), (1, 32)]
    (codeMat 334) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane426GenSource0049 :
    QuotientRankAtLeast (spanCodes [272, 150, 112, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(272, 435), (150, 434), (112, 43), (10, 316), (1, 32)]
    (codeMat 125) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
