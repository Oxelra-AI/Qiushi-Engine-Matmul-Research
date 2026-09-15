import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit166Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0050 :
    QuotientRankAtLeast (spanCodes [261, 160, 103, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(261, 97), (160, 21), (103, 443), (20, 338), (10, 475)]
    (codeMat 230) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane458GenSource0051 :
    QuotientRankAtLeast (spanCodes [290, 128, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 10), (128, 32), (96, 310), (20, 43), (10, 408)]
    (codeMat 311) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane458GenSource0052 :
    QuotientRankAtLeast (spanCodes [290, 132, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(290, 10), (132, 30), (100, 343), (20, 31), (10, 291)]
    (codeMat 190) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane458GenSource0053 :
    QuotientRankAtLeast (spanCodes [290, 134, 102, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(290, 257), (134, 97), (102, 116), (20, 353), (10, 287)]
    (codeMat 486) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane458GenSource0054 :
    QuotientRankAtLeast (spanCodes [290, 162, 66, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(290, 31), (162, 30), (66, 127), (20, 21), (10, 383)]
    (codeMat 412) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane458GenSource0055 :
    QuotientRankAtLeast (spanCodes [290, 165, 69, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(290, 463), (165, 253), (69, 294), (20, 430), (10, 232)]
    (codeMat 303) (codeMat 380) (codeMat 117) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane458GenSource0056 :
    QuotientRankAtLeast (spanCodes [257, 195, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(257, 497), (195, 1), (35, 42), (20, 383), (10, 133)]
    (codeMat 477) (codeMat 229) (codeMat 187) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane458GenSource0057 :
    QuotientRankAtLeast (spanCodes [261, 129, 70, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(261, 80), (129, 240), (70, 280), (39, 322), (20, 262), (10, 323)]
    (codeMat 99) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane458GenSource0058 :
    QuotientRankAtLeast (spanCodes [256, 194, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 32), (194, 164), (35, 42), (20, 464), (10, 383)]
    (codeMat 271) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane458GenSource0059 :
    QuotientRankAtLeast (spanCodes [288, 134, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(288, 32), (134, 43), (100, 440), (20, 42), (10, 133)]
    (codeMat 407) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
