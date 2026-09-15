import QiushiPlane473GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane473GenSource0110 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 21), (128, 1), (64, 2), (36, 360), (20, 104), (8, 128), (2, 8)]
    (codeMat 140) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0111 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 37, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (129, 149), (64, 2), (37, 138), (20, 284), (8, 130), (2, 511)]
    (codeMat 412) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0112 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (129, 129), (65, 1), (37, 97), (21, 414), (9, 8), (3, 130)]
    (codeMat 285) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0113 :
    QuotientRankAtLeast (spanCodes [261, 129, 69, 32, 17, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 227), (129, 138), (69, 284), (32, 256), (17, 131), (9, 3), (3, 130)]
    (codeMat 171) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0114 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 33, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (132, 363), (65, 1), (33, 138), (21, 276), (9, 8), (3, 511)]
    (codeMat 477) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0115 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (128, 384), (65, 9), (37, 105), (21, 235), (9, 8), (3, 511)]
    (codeMat 286) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0116 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 22), (128, 3), (64, 2), (36, 384), (20, 232), (9, 128), (3, 8)]
    (codeMat 204) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0117 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (129, 264), (65, 8), (37, 510), (21, 509), (8, 1), (2, 360)]
    (codeMat 298) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane473GenSource0118 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 70), (129, 68), (64, 1), (36, 432), (20, 416), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane473GenSource0119 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 119), (130, 9), (70, 245), (34, 392), (18, 8), (10, 264), (1, 360)]
    (codeMat 158) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
