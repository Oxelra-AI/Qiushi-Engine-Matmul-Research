import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0160 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (128, 9), (68, 413), (36, 384), (16, 8), (10, 96), (1, 360)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0161 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 252), (134, 483), (66, 404), (32, 511), (20, 227), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0162 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 488), (130, 360), (66, 104), (36, 511), (20, 381), (10, 105), (1, 8)]
    (codeMat 270) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0163 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 126), (132, 119), (66, 278), (32, 511), (22, 503), (10, 276), (1, 130)]
    (codeMat 478) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0164 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 71), (132, 70), (70, 324), (34, 440), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane425GenSource0165 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 228), (130, 219), (66, 210), (32, 32), (18, 216), (10, 208), (1, 128)]
    (codeMat 86) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane425GenSource0166 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 100), (128, 9), (66, 82), (32, 32), (16, 8), (10, 80), (1, 128)]
    (codeMat 86) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane425GenSource0167 :
    QuotientRankAtLeast (spanCodes [258, 132, 66, 34, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 413), (132, 245), (66, 404), (34, 414), (22, 373), (10, 406), (1, 130)]
    (codeMat 470) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0168 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 287), (134, 483), (66, 278), (34, 284), (20, 227), (10, 276), (1, 130)]
    (codeMat 470) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0169 :
    QuotientRankAtLeast (spanCodes [256, 132, 80, 36, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (132, 96), (80, 276), (36, 1), (8, 130), (2, 256), (1, 128)]
    (codeMat 99) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
