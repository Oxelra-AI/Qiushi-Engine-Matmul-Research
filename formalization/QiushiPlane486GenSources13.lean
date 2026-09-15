import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit29FP
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0130 :
    QuotientRankAtLeast (spanCodes [288, 161, 68, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(288, 16), (161, 334), (68, 209), (9, 192), (3, 36)]
    (codeMat 247) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane486GenSource0131 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 10), (128, 32), (65, 2), (10, 164), (5, 9)]
    (codeMat 165) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0132 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 10), (129, 34), (65, 2), (10, 164), (5, 9)]
    (codeMat 229) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0133 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 52), (130, 54), (64, 1), (10, 112), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane486GenSource0134 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 1), (130, 32), (64, 2), (10, 164), (4, 9)]
    (codeMat 172) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0135 :
    QuotientRankAtLeast (spanCodes [256, 131, 64, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 1), (131, 34), (64, 2), (10, 164), (4, 9)]
    (codeMat 236) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane486GenSource0136 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 20), (128, 2), (64, 1), (10, 80), (4, 32), (1, 8)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane486GenSource0137 :
    QuotientRankAtLeast (spanCodes [276, 132, 68, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(276, 246), (132, 30), (68, 22), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0138 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(260, 32), (128, 2), (68, 33), (33, 265), (10, 383)]
    (codeMat 236) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane486GenSource0139 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (160, 68), (64, 2), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
