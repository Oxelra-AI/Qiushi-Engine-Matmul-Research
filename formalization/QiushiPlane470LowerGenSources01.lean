import QiushiPlane470LowerGenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit166Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit216Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470LowerGenSource0010 :
    QuotientRankAtLeast (spanCodes [259, 64, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(259, 441), (64, 1), (37, 20), (20, 274), (10, 434)]
    (codeMat 156) (codeMat 183) (codeMat 419) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane470LowerGenSource0011 :
    QuotientRankAtLeast (spanCodes [259, 71, 33, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 352), (71, 136), (33, 21), (19, 38), (10, 50)]
    (codeMat 266) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470LowerGenSource0012 :
    QuotientRankAtLeast (spanCodes [259, 71, 32, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(259, 456), (71, 424), (32, 1), (19, 450), (10, 133)]
    (codeMat 98) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane470LowerGenSource0013 :
    QuotientRankAtLeast (spanCodes [259, 66, 37, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 475), (66, 508), (37, 21), (22, 175), (10, 509)]
    (codeMat 286) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470LowerGenSource0014 :
    QuotientRankAtLeast (spanCodes [259, 64, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 127), (64, 256), (32, 1), (20, 10), (10, 31)]
    (codeMat 282) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470LowerGenSource0015 :
    QuotientRankAtLeast (spanCodes [259, 81, 49, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(259, 127), (81, 316), (49, 296), (10, 97), (5, 1)]
    (codeMat 177) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane470LowerGenSource0016 :
    QuotientRankAtLeast (spanCodes [259, 82, 50, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 132), (82, 350), (50, 11), (10, 43), (6, 1)]
    (codeMat 337) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane470LowerGenSource0017 :
    QuotientRankAtLeast (spanCodes [259, 71, 37, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 475), (71, 137), (37, 21), (19, 20), (10, 38)]
    (codeMat 339) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470LowerGenSource0018 :
    QuotientRankAtLeast (spanCodes [259, 66, 33, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(259, 280), (66, 263), (33, 20), (22, 422), (10, 262)]
    (codeMat 86) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane470LowerGenSource0019 :
    QuotientRankAtLeast (spanCodes [259, 64, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 496), (64, 1), (35, 464), (20, 341), (10, 506)]
    (codeMat 412) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
