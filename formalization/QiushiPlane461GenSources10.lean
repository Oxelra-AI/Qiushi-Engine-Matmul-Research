import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0100 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 36, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 100), (132, 274), (68, 301), (36, 32), (21, 208), (8, 360), (2, 128)]
    (codeMat 95) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane461GenSource0101 :
    QuotientRankAtLeast (spanCodes [256, 129, 68, 33, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 390), (129, 450), (68, 197), (33, 240), (21, 80), (8, 360), (2, 128)]
    (codeMat 93) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane461GenSource0102 :
    QuotientRankAtLeast (spanCodes [262, 132, 68, 38, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 263), (132, 451), (68, 450), (38, 312), (22, 280), (10, 208), (1, 128)]
    (codeMat 84) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane461GenSource0103 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 32, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 228), (130, 219), (68, 274), (32, 32), (20, 280), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane461GenSource0104 :
    QuotientRankAtLeast (spanCodes [132, 68, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(132, 198), (68, 70), (36, 54), (20, 30), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane461GenSource0105 :
    QuotientRankAtLeast (spanCodes [129, 65, 33, 16, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(129, 88), (65, 216), (33, 30), (16, 1), (8, 3), (5, 40), (2, 8)]
    (codeMat 266) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane461GenSource0106 :
    QuotientRankAtLeast (spanCodes [129, 64, 33, 16, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(129, 80), (64, 128), (33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane461GenSource0107 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (134, 70), (68, 324), (36, 8), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane461GenSource0108 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 112), (128, 216), (65, 32), (34, 198), (16, 3), (10, 196), (5, 128)]
    (codeMat 106) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane461GenSource0109 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 374), (129, 265), (65, 256), (35, 138), (17, 97), (10, 105), (5, 511)]
    (codeMat 351) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
