import QiushiGlobalOrbitUnused321Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane321UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 146, 64, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 16), (146, 432), (64, 2), (50, 264), (10, 77), (4, 8), (1, 1)]
    (codeMat 225) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane321UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [256, 146, 82, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (146, 511), (82, 381), (50, 361), (10, 105), (4, 1), (1, 8)]
    (codeMat 161) (codeMat 158) (codeMat 358) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [288, 160, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 432), (160, 424), (64, 3), (18, 256), (10, 69), (6, 8), (1, 1)]
    (codeMat 233) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane321UnusedGenSource0033 :
    QuotientRankAtLeast (spanCodes [272, 130, 66, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 168), (130, 432), (66, 79), (34, 264), (10, 77), (6, 8), (1, 1)]
    (codeMat 241) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane321UnusedGenSource0034 :
    QuotientRankAtLeast (spanCodes [272, 130, 80, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 148), (130, 511), (80, 276), (34, 361), (10, 105), (6, 1), (1, 8)]
    (codeMat 177) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0035 :
    QuotientRankAtLeast (spanCodes [258, 144, 66, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 361), (144, 256), (66, 150), (48, 9), (10, 22), (6, 1), (1, 2)]
    (codeMat 409) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0036 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 361), (144, 256), (80, 255), (48, 9), (10, 31), (6, 1), (1, 3)]
    (codeMat 409) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 144, 82, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 257), (144, 360), (82, 235), (48, 9), (10, 30), (6, 1), (1, 3)]
    (codeMat 345) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane321UnusedGenSource0038 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 32, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 91), (128, 128), (68, 457), (32, 1), (20, 11), (10, 21), (1, 63)]
    (codeMat 282) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane321UnusedGenSource0039 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (130, 8), (66, 352), (34, 31), (20, 28), (10, 480), (1, 256)]
    (codeMat 117) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
