import QiushiPlane463LowerGenData
import QiushiCertifiedTransport
import QiushiWcOrbit140Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463LowerGenSource0040 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 10), (134, 11), (68, 30), (53, 127), (10, 383)]
    (codeMat 236) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463LowerGenSource0041 :
    QuotientRankAtLeast (spanCodes [262, 129, 68, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 175), (129, 186), (68, 488), (50, 462), (10, 463)]
    (codeMat 482) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane463LowerGenSource0042 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 257), (128, 256), (68, 353), (51, 362), (10, 383)]
    (codeMat 285) (codeMat 397) (codeMat 250) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463LowerGenSource0043 :
    QuotientRankAtLeast (spanCodes [262, 131, 68, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 327), (131, 186), (68, 488), (48, 1), (10, 463)]
    (codeMat 426) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane463LowerGenSource0044 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 96), (130, 256), (68, 353), (49, 21), (10, 383)]
    (codeMat 348) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463LowerGenSource0045 :
    QuotientRankAtLeast (spanCodes [177, 64, 8, 4, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 84, 32, 2, 1] [(177, 84), (64, 32), (8, 256), (4, 3), (2, 2)]
    (codeMat 161) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit140_lb14_wc

theorem plane463LowerGenSource0046 :
    QuotientRankAtLeast (spanCodes [176, 65, 9, 5, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 84, 32, 2, 1] [(176, 119), (65, 32), (9, 256), (5, 3), (3, 2)]
    (codeMat 233) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit140_lb14_wc

theorem plane463LowerGenSource0047 :
    QuotientRankAtLeast (spanCodes [176, 64, 9, 4, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 84, 32, 2, 1] [(176, 373), (64, 32), (9, 256), (4, 3), (3, 2)]
    (codeMat 225) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit140_lb14_wc

theorem plane463LowerGenSource0048 :
    QuotientRankAtLeast (spanCodes [177, 65, 8, 5, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 84, 32, 2, 1] [(177, 342), (65, 32), (8, 256), (5, 3), (2, 2)]
    (codeMat 169) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit140_lb14_wc

end QiushiMatmul
