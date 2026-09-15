import QiushiPlane463LowerGenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463LowerGenSource0030 :
    QuotientRankAtLeast (spanCodes [262, 148, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 475), (148, 338), (68, 39), (39, 462), (10, 463)]
    (codeMat 379) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane463LowerGenSource0031 :
    QuotientRankAtLeast (spanCodes [262, 151, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 508), (151, 338), (68, 39), (36, 1), (10, 463)]
    (codeMat 307) (codeMat 158) (codeMat 358) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane463LowerGenSource0032 :
    QuotientRankAtLeast (spanCodes [262, 150, 68, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 373), (150, 97), (68, 30), (37, 21), (10, 383)]
    (codeMat 407) (codeMat 187) (codeMat 229) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463LowerGenSource0033 :
    QuotientRankAtLeast (spanCodes [262, 145, 68, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 126), (145, 21), (68, 353), (34, 127), (10, 383)]
    (codeMat 183) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463LowerGenSource0034 :
    QuotientRankAtLeast (spanCodes [262, 144, 68, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 352), (144, 1), (68, 488), (35, 373), (10, 463)]
    (codeMat 270) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane463LowerGenSource0035 :
    QuotientRankAtLeast (spanCodes [262, 147, 68, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 287), (147, 21), (68, 353), (32, 256), (10, 383)]
    (codeMat 190) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463LowerGenSource0036 :
    QuotientRankAtLeast (spanCodes [262, 146, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 136), (146, 1), (68, 488), (33, 186), (10, 463)]
    (codeMat 335) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane463LowerGenSource0037 :
    QuotientRankAtLeast (spanCodes [262, 133, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 20), (133, 11), (68, 30), (54, 256), (10, 383)]
    (codeMat 229) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463LowerGenSource0038 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 20), (132, 38), (68, 39), (55, 186), (10, 463)]
    (codeMat 460) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane463LowerGenSource0039 :
    QuotientRankAtLeast (spanCodes [262, 135, 68, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(262, 51), (135, 38), (68, 39), (52, 373), (10, 463)]
    (codeMat 397) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

end QiushiMatmul
