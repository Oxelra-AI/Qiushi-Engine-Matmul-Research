import QiushiGlobalOrbitUnused371Data
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane371UnusedGenSource0030 :
    QuotientRankAtLeast (spanCodes [290, 130, 98, 18, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(290, 502), (130, 256), (98, 158), (18, 128), (8, 3), (6, 9), (1, 1)]
    (codeMat 345) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane371UnusedGenSource0031 :
    QuotientRankAtLeast (spanCodes [266, 136, 64, 40, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(266, 372), (136, 224), (64, 256), (40, 511), (18, 360), (6, 130), (1, 128)]
    (codeMat 271) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane371UnusedGenSource0032 :
    QuotientRankAtLeast (spanCodes [266, 130, 74, 40, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(266, 205), (130, 130), (74, 21), (40, 219), (18, 128), (6, 54), (1, 63)]
    (codeMat 254) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane371UnusedGenSource0033 :
    QuotientRankAtLeast (spanCodes [264, 138, 64, 42, 18, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 480), (138, 246), (64, 256), (42, 10), (18, 9), (6, 130), (1, 128)]
    (codeMat 267) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane371UnusedGenSource0034 :
    QuotientRankAtLeast (spanCodes [258, 134, 70, 32, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 90), (134, 139), (70, 483), (32, 1), (20, 11), (10, 21), (1, 63)]
    (codeMat 474) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane371UnusedGenSource0035 :
    QuotientRankAtLeast (spanCodes [256, 132, 70, 34, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 1), (132, 11), (70, 80), (34, 20), (20, 52), (10, 402), (1, 128)]
    (codeMat 204) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane371UnusedGenSource0036 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 36, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(262, 197), (130, 390), (70, 429), (36, 1), (20, 129), (10, 81), (1, 219)]
    (codeMat 467) (codeMat 207) (codeMat 370) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane371UnusedGenSource0037 :
    QuotientRankAtLeast (spanCodes [260, 128, 70, 38, 20, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(260, 63), (128, 360), (70, 450), (38, 139), (20, 90), (10, 208), (1, 128)]
    (codeMat 394) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
