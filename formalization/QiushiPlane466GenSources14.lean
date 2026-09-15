import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0140 :
    QuotientRankAtLeast (spanCodes [258, 132, 68, 33, 18, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 316), (132, 284), (68, 287), (33, 441), (18, 438), (10, 439)]
    (codeMat 370) (codeMat 478) (codeMat 445) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane466GenSource0141 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 35, 16, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 68), (131, 197), (67, 323), (35, 160), (16, 360), (10, 408), (7, 128)]
    (codeMat 93) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane466GenSource0142 :
    QuotientRankAtLeast (spanCodes [261, 128, 68, 32, 20, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 100), (128, 63), (68, 301), (32, 32), (20, 312), (9, 360), (3, 128)]
    (codeMat 86) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane466GenSource0143 :
    QuotientRankAtLeast (spanCodes [256, 65, 33, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (65, 216), (33, 10), (16, 54), (9, 3), (5, 8), (3, 40)]
    (codeMat 267) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0144 :
    QuotientRankAtLeast (spanCodes [257, 64, 32, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 80), (64, 128), (32, 9), (16, 54), (9, 2), (4, 8), (3, 32)]
    (codeMat 267) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0145 :
    QuotientRankAtLeast (spanCodes [258, 64, 32, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 70), (64, 128), (32, 8), (18, 54), (10, 22), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0146 :
    QuotientRankAtLeast (spanCodes [260, 68, 32, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 216), (68, 88), (32, 3), (20, 28), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0147 :
    QuotientRankAtLeast (spanCodes [292, 132, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(292, 54), (132, 78), (68, 150), (20, 70), (8, 128), (2, 1), (1, 2)]
    (codeMat 177) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0148 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 60), (129, 138), (64, 219), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 143) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0149 :
    QuotientRankAtLeast (spanCodes [290, 130, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(290, 30), (130, 219), (66, 89), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 142) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
