import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0160 :
    QuotientRankAtLeast (spanCodes [256, 133, 68, 33, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 219), (133, 274), (68, 429), (33, 408), (20, 80), (8, 360), (2, 128)]
    (codeMat 94) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0161 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 38, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 374), (130, 219), (68, 402), (38, 240), (22, 408), (10, 80), (1, 128)]
    (codeMat 95) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0162 :
    QuotientRankAtLeast (spanCodes [262, 130, 68, 36, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 69), (130, 1), (68, 450), (36, 360), (20, 328), (10, 80), (1, 128)]
    (codeMat 85) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane462GenSource0163 :
    QuotientRankAtLeast (spanCodes [128, 68, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(128, 128), (68, 70), (36, 54), (20, 22), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0164 :
    QuotientRankAtLeast (spanCodes [129, 65, 33, 16, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(129, 88), (65, 216), (33, 30), (16, 1), (8, 3), (5, 40), (2, 8)]
    (codeMat 266) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0165 :
    QuotientRankAtLeast (spanCodes [128, 65, 32, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(128, 128), (65, 216), (32, 54), (17, 10), (9, 3), (5, 40), (3, 8)]
    (codeMat 267) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0166 :
    QuotientRankAtLeast (spanCodes [129, 64, 33, 17, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(129, 208), (64, 128), (33, 52), (17, 11), (9, 2), (4, 32), (3, 8)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0167 :
    QuotientRankAtLeast (spanCodes [129, 64, 33, 16, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(129, 80), (64, 128), (33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0168 :
    QuotientRankAtLeast (spanCodes [132, 68, 32, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(132, 196), (68, 68), (32, 32), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0169 :
    QuotientRankAtLeast (spanCodes [258, 162, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 487), (162, 228), (66, 162), (16, 256), (10, 160), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
