import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit212Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit235Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit374Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0000 :
    QuotientRankAtLeast (spanCodes [311, 164, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(311, 161), (164, 245), (84, 85), (10, 283)]
    (codeMat 181) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane468GenSource0001 :
    QuotientRankAtLeast (spanCodes [129, 81, 32, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 133), (81, 341), (32, 32), (10, 42), (5, 1)]
    (codeMat 273) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane468GenSource0002 :
    QuotientRankAtLeast (spanCodes [129, 66, 37, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 11), (66, 10), (37, 341), (22, 175), (10, 42)]
    (codeMat 397) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane468GenSource0003 :
    QuotientRankAtLeast (spanCodes [133, 66, 33, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(133, 350), (66, 43), (33, 506), (22, 383), (10, 42)]
    (codeMat 478) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane468GenSource0004 :
    QuotientRankAtLeast (spanCodes [135, 64, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(135, 137), (64, 1), (35, 488), (20, 175), (10, 21)]
    (codeMat 460) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane468GenSource0005 :
    QuotientRankAtLeast (spanCodes [147, 81, 50, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(147, 341), (81, 133), (50, 43), (10, 42), (5, 32)]
    (codeMat 330) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane468GenSource0006 :
    QuotientRankAtLeast (spanCodes [259, 163, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 505), (163, 239), (83, 381), (10, 97), (7, 1)]
    (codeMat 177) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane468GenSource0007 :
    QuotientRankAtLeast (spanCodes [257, 162, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(257, 97), (162, 21), (82, 306), (10, 462), (6, 1)]
    (codeMat 313) (codeMat 115) (codeMat 492) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane468GenSource0008 :
    QuotientRankAtLeast (spanCodes [261, 164, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(261, 11), (164, 238), (65, 1), (21, 381), (10, 97)]
    (codeMat 397) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane468GenSource0009 :
    QuotientRankAtLeast (spanCodes [262, 164, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 132, 96, 10, 1] [(262, 509), (164, 376), (65, 1), (21, 228), (10, 502)]
    (codeMat 253) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit212_lb16_wc

end QiushiMatmul
