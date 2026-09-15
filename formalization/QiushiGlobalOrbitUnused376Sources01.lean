import QiushiGlobalOrbitUnused376Data
import QiushiCertifiedTransport
import QiushiMonoOrbit74From17
import QiushiOrbit14FP
import QiushiOrbit29FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane376UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(160, 160), (68, 68), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane376UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [131, 64, 35, 19, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 192, 32, 20, 10, 1] [(131, 31), (64, 32), (35, 347), (19, 30), (10, 43), (4, 192)]
    (codeMat 318) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit74_lb14_mono

theorem plane376UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 374), (129, 255), (65, 256), (33, 353), (19, 252), (10, 287), (5, 9)]
    (codeMat 375) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane376UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 352), (128, 256), (66, 224), (32, 9), (19, 252), (10, 287), (6, 360)]
    (codeMat 303) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane376UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 503), (130, 511), (67, 284), (34, 119), (19, 252), (10, 287), (7, 130)]
    (codeMat 423) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
