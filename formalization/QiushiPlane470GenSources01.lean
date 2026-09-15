import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit166Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0010 :
    QuotientRankAtLeast (spanCodes [259, 65, 34, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(259, 368), (65, 288), (34, 21), (21, 10), (10, 20)]
    (codeMat 266) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane470GenSource0011 :
    QuotientRankAtLeast (spanCodes [259, 64, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 496), (64, 1), (35, 464), (20, 341), (10, 506)]
    (codeMat 412) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane470GenSource0012 :
    QuotientRankAtLeast (spanCodes [259, 81, 50, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 392), (81, 133), (50, 43), (10, 42), (5, 32)]
    (codeMat 330) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane470GenSource0013 :
    QuotientRankAtLeast (spanCodes [259, 128, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 96), (128, 1), (80, 10), (10, 31), (4, 256)]
    (codeMat 116) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470GenSource0014 :
    QuotientRankAtLeast (spanCodes [259, 129, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 39), (129, 21), (81, 175), (10, 327), (5, 1)]
    (codeMat 225) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470GenSource0015 :
    QuotientRankAtLeast (spanCodes [259, 130, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(259, 367), (130, 1), (81, 11), (10, 80), (5, 288)]
    (codeMat 213) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane470GenSource0016 :
    QuotientRankAtLeast (spanCodes [259, 132, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(259, 31), (132, 21), (65, 1), (21, 349), (10, 97)]
    (codeMat 397) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane470GenSource0017 :
    QuotientRankAtLeast (spanCodes [259, 135, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 133), (135, 386), (65, 1), (21, 418), (10, 269)]
    (codeMat 317) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane470GenSource0018 :
    QuotientRankAtLeast (spanCodes [259, 134, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 132), (134, 387), (65, 1), (21, 175), (10, 269)]
    (codeMat 309) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane470GenSource0019 :
    QuotientRankAtLeast (spanCodes [259, 145, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(259, 79), (145, 90), (81, 91), (10, 80), (5, 288)]
    (codeMat 156) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

end QiushiMatmul
