import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit166Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0000 :
    QuotientRankAtLeast (spanCodes [259, 69, 32, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 301), (69, 164), (32, 32), (17, 10), (10, 11)]
    (codeMat 339) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane470GenSource0001 :
    QuotientRankAtLeast (spanCodes [259, 65, 36, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(259, 80), (65, 288), (36, 1), (21, 30), (10, 20)]
    (codeMat 267) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane470GenSource0002 :
    QuotientRankAtLeast (spanCodes [259, 67, 38, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 164), (67, 132), (38, 175), (23, 341), (10, 133)]
    (codeMat 271) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane470GenSource0003 :
    QuotientRankAtLeast (spanCodes [259, 65, 38, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 353), (65, 1), (38, 338), (21, 488), (10, 327)]
    (codeMat 285) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470GenSource0004 :
    QuotientRankAtLeast (spanCodes [259, 64, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 127), (64, 256), (32, 1), (20, 10), (10, 31)]
    (codeMat 282) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470GenSource0005 :
    QuotientRankAtLeast (spanCodes [259, 65, 33, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 352), (65, 1), (33, 21), (21, 175), (10, 327)]
    (codeMat 277) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470GenSource0006 :
    QuotientRankAtLeast (spanCodes [259, 71, 39, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 133), (71, 175), (39, 132), (19, 310), (10, 164)]
    (codeMat 207) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane470GenSource0007 :
    QuotientRankAtLeast (spanCodes [259, 81, 49, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(259, 127), (81, 316), (49, 296), (10, 97), (5, 1)]
    (codeMat 177) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane470GenSource0008 :
    QuotientRankAtLeast (spanCodes [259, 82, 50, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 132), (82, 350), (50, 11), (10, 43), (6, 1)]
    (codeMat 337) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane470GenSource0009 :
    QuotientRankAtLeast (spanCodes [259, 81, 51, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 424), (81, 175), (51, 33), (10, 42), (5, 32)]
    (codeMat 267) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

end QiushiMatmul
