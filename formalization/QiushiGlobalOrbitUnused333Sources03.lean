import QiushiGlobalOrbitUnused333Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit13FP
import QiushiPlane315GenBindings01
import QiushiStep81Qdim2Generated
import QiushiWcOrbit161Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane333UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [268, 136, 70, 38, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(268, 272), (136, 475), (70, 357), (38, 193), (16, 192), (1, 260)]
    (codeMat 171) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0017

theorem plane333UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [256, 132, 74, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(256, 1), (132, 78), (74, 180), (42, 240), (16, 384), (1, 288)]
    (codeMat 156) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc161s4Dispatch

theorem plane333UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [260, 136, 78, 46, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 432), (136, 283), (78, 97), (46, 453), (16, 192), (1, 260)]
    (codeMat 187) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0017

theorem plane333UnusedGenSource0033 :
    QuotientRankAtLeast (spanCodes [288, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (132, 168), (96, 69), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane333UnusedGenSource0034 :
    QuotientRankAtLeast (spanCodes [292, 132, 96, 16, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 68, 160, 256] [(292, 256), (132, 76), (96, 180), (16, 9), (12, 22), (2, 1), (1, 2)]
    (codeMat 473) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit13_lb12

theorem plane333UnusedGenSource0035 :
    QuotientRankAtLeast (spanCodes [288, 130, 96, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 12, 2, 1] [(288, 438), (130, 256), (96, 113), (16, 32), (10, 12), (6, 2), (1, 1)]
    (codeMat 337) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o16s2Span_lb

end QiushiMatmul
