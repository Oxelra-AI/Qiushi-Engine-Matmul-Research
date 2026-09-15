import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep81Qdim2Generated
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0120 :
    QuotientRankAtLeast (spanCodes [263, 129, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 224), (129, 227), (68, 255), (39, 96), (17, 97), (10, 105)]
    (codeMat 115) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0121 :
    QuotientRankAtLeast (spanCodes [293, 160, 68, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(293, 79), (160, 258), (68, 113), (20, 310), (9, 63), (3, 365)]
    (codeMat 174) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane466GenSource0122 :
    QuotientRankAtLeast (spanCodes [290, 164, 68, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(290, 430), (164, 238), (68, 160), (18, 27), (10, 26), (1, 16)]
    (codeMat 330) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane466GenSource0123 :
    QuotientRankAtLeast (spanCodes [304, 176, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 104), (176, 96), (66, 21), (10, 149), (6, 1), (1, 2)]
    (codeMat 417) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0124 :
    QuotientRankAtLeast (spanCodes [304, 178, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 224), (178, 104), (64, 3), (10, 148), (4, 128), (1, 2)]
    (codeMat 141) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0125 :
    QuotientRankAtLeast (spanCodes [257, 68, 36, 20, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(257, 274), (68, 164), (36, 32), (20, 33), (8, 2), (2, 45)]
    (codeMat 282) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane466GenSource0126 :
    QuotientRankAtLeast (spanCodes [292, 129, 68, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(292, 45), (129, 272), (68, 408), (21, 316), (8, 438), (2, 32)]
    (codeMat 334) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane466GenSource0127 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 33, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(261, 263), (132, 322), (68, 196), (33, 312), (21, 208), (8, 32), (2, 128)]
    (codeMat 85) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane466GenSource0128 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 35, 16, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(258, 274), (131, 228), (64, 63), (35, 208), (16, 32), (10, 312), (4, 128)]
    (codeMat 86) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane466GenSource0129 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 33, 19, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(259, 450), (130, 390), (64, 1), (33, 208), (19, 112), (10, 456), (4, 128)]
    (codeMat 92) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

end QiushiMatmul
