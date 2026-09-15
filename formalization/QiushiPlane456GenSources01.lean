import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0010 :
    QuotientRankAtLeast (spanCodes [256, 132, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 1), (132, 10), (37, 133), (20, 42), (10, 341)]
    (codeMat 396) (codeMat 85) (codeMat 340) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(262, 10), (130, 1), (35, 160), (20, 20), (10, 262)]
    (codeMat 141) (codeMat 99) (codeMat 172) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane456GenSource0012 :
    QuotientRankAtLeast (spanCodes [259, 132, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 350), (132, 43), (37, 383), (20, 42), (10, 506)]
    (codeMat 478) (codeMat 111) (codeMat 412) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0013 :
    QuotientRankAtLeast (spanCodes [261, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(261, 164), (130, 32), (35, 175), (20, 42), (10, 464)]
    (codeMat 334) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0014 :
    QuotientRankAtLeast (spanCodes [291, 161, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(291, 496), (161, 165), (17, 10), (10, 11), (5, 32)]
    (codeMat 459) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0015 :
    QuotientRankAtLeast (spanCodes [256, 161, 65, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(256, 1), (161, 499), (65, 504), (20, 132), (10, 278)]
    (codeMat 212) (codeMat 206) (codeMat 498) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456GenSource0016 :
    QuotientRankAtLeast (spanCodes [258, 161, 67, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(258, 472), (161, 239), (67, 96), (20, 316), (10, 97)]
    (codeMat 335) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane456GenSource0017 :
    QuotientRankAtLeast (spanCodes [288, 161, 98, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(288, 1), (161, 239), (98, 279), (20, 97), (10, 284)]
    (codeMat 470) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456GenSource0018 :
    QuotientRankAtLeast (spanCodes [258, 161, 65, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 97), (161, 474), (65, 1), (20, 430), (10, 326)]
    (codeMat 317) (codeMat 423) (codeMat 181) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane456GenSource0019 :
    QuotientRankAtLeast (spanCodes [259, 161, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 287), (161, 116), (64, 256), (20, 362), (10, 383)]
    (codeMat 279) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
