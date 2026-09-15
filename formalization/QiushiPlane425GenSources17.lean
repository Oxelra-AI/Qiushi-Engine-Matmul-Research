import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0170 :
    QuotientRankAtLeast (spanCodes [256, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (164, 228), (68, 160), (16, 3), (8, 2), (2, 24), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane425GenSource0171 :
    QuotientRankAtLeast (spanCodes [256, 132, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (132, 149), (96, 96), (20, 21), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0172 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 413), (132, 245), (66, 404), (38, 414), (20, 373), (10, 276), (1, 130)]
    (codeMat 415) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0173 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 287), (134, 483), (66, 278), (38, 284), (22, 227), (10, 406), (1, 130)]
    (codeMat 415) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0174 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 71), (132, 70), (70, 324), (38, 440), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane425GenSource0175 :
    QuotientRankAtLeast (spanCodes [258, 146, 80, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 257), (146, 360), (80, 235), (48, 8), (10, 29), (6, 1), (1, 3)]
    (codeMat 337) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0176 :
    QuotientRankAtLeast (spanCodes [258, 130, 82, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 129), (130, 3), (82, 284), (34, 136), (10, 480), (6, 128), (1, 256)]
    (codeMat 93) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0177 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 252), (134, 483), (66, 404), (36, 511), (22, 227), (10, 276), (1, 130)]
    (codeMat 407) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0178 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 488), (130, 360), (66, 104), (32, 511), (22, 381), (10, 97), (1, 8)]
    (codeMat 271) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0179 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (132, 119), (66, 278), (36, 511), (20, 503), (10, 406), (1, 130)]
    (codeMat 407) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
