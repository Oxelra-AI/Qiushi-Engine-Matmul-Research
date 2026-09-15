import QiushiPlane434GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane434GenSource0050 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 34, 16, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 323), (134, 197), (66, 450), (34, 408), (16, 360), (12, 80), (1, 128)]
    (codeMat 93) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane434GenSource0051 :
    QuotientRankAtLeast (spanCodes [266, 130, 78, 46, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(266, 275), (130, 1), (78, 160), (46, 315), (16, 9), (1, 432)]
    (codeMat 445) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane434GenSource0052 :
    QuotientRankAtLeast (spanCodes [266, 136, 72, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 486), (136, 324), (72, 1), (34, 416), (16, 256), (6, 16), (1, 8)]
    (codeMat 142) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane434GenSource0053 :
    QuotientRankAtLeast (spanCodes [266, 130, 74, 42, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(266, 230), (130, 130), (74, 61), (42, 208), (16, 128), (6, 32), (1, 40)]
    (codeMat 143) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane434GenSource0054 :
    QuotientRankAtLeast (spanCodes [262, 130, 66, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 70), (130, 1), (66, 324), (36, 432), (16, 8), (12, 416), (1, 256)]
    (codeMat 85) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane434GenSource0055 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 38, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 235), (134, 373), (66, 276), (38, 387), (16, 384), (8, 128), (1, 130)]
    (codeMat 171) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane434GenSource0056 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (132, 237), (70, 82), (38, 240), (16, 40), (14, 208), (1, 128)]
    (codeMat 87) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane434GenSource0057 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 38, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 21), (134, 23), (64, 1), (38, 381), (16, 511), (12, 97), (1, 8)]
    (codeMat 460) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane434GenSource0058 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (128, 3), (68, 324), (38, 424), (16, 24), (14, 416), (1, 256)]
    (codeMat 84) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane434GenSource0059 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(262, 326), (128, 3), (70, 324), (36, 432), (16, 24), (12, 416), (1, 256)]
    (codeMat 84) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
