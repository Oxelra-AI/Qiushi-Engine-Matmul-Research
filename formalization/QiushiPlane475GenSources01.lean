import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0010 :
    QuotientRankAtLeast (spanCodes [259, 161, 96, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 10), (161, 116), (96, 97), (10, 362), (4, 1)]
    (codeMat 481) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane475GenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 164, 96, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(262, 278), (164, 441), (96, 43), (10, 284), (1, 32)]
    (codeMat 111) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane475GenSource0012 :
    QuotientRankAtLeast (spanCodes [273, 165, 96, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(273, 380), (165, 285), (96, 278), (9, 504), (3, 1)]
    (codeMat 417) (codeMat 478) (codeMat 445) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane475GenSource0013 :
    QuotientRankAtLeast (spanCodes [256, 165, 96, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(256, 432), (165, 142), (96, 238), (19, 319), (10, 475)]
    (codeMat 111) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane475GenSource0014 :
    QuotientRankAtLeast (spanCodes [275, 162, 96, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(275, 499), (162, 10), (96, 402), (10, 238), (7, 504)]
    (codeMat 303) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane475GenSource0015 :
    QuotientRankAtLeast (spanCodes [263, 165, 96, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(263, 408), (165, 174), (96, 133), (17, 316), (10, 284)]
    (codeMat 247) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane475GenSource0016 :
    QuotientRankAtLeast (spanCodes [263, 165, 96, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(263, 175), (165, 311), (96, 434), (16, 32), (10, 284)]
    (codeMat 167) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane475GenSource0017 :
    QuotientRankAtLeast (spanCodes [259, 135, 66, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 175), (135, 464), (66, 133), (34, 164), (10, 132)]
    (codeMat 142) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane475GenSource0018 :
    QuotientRankAtLeast (spanCodes [278, 146, 87, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(278, 463), (146, 1), (87, 307), (55, 232), (10, 136)]
    (codeMat 159) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane475GenSource0019 :
    QuotientRankAtLeast (spanCodes [262, 128, 69, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 33), (128, 32), (69, 42), (37, 383), (10, 475)]
    (codeMat 229) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
