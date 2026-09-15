import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit41FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0040 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 510), (144, 384), (80, 232), (48, 8), (10, 30), (6, 1), (1, 3)]
    (codeMat 401) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0041 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (130, 9), (66, 210), (34, 112), (16, 8), (10, 80), (1, 128)]
    (codeMat 87) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane315GenSource0042 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (132, 392), (68, 264), (36, 1), (16, 511), (10, 149), (1, 360)]
    (codeMat 299) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0043 :
    QuotientRankAtLeast (spanCodes [260, 160, 98, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(260, 32), (160, 476), (98, 84), (18, 511), (10, 502), (1, 384)]
    (codeMat 111) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane315GenSource0044 :
    QuotientRankAtLeast (spanCodes [260, 134, 66, 38, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (134, 245), (66, 404), (38, 235), (20, 373), (10, 406), (1, 130)]
    (codeMat 470) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0045 :
    QuotientRankAtLeast (spanCodes [260, 132, 66, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (132, 353), (66, 404), (36, 8), (22, 97), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0046 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (134, 224), (68, 264), (38, 508), (16, 511), (10, 149), (1, 360)]
    (codeMat 355) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0047 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (132, 326), (70, 68), (36, 24), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane315GenSource0048 :
    QuotientRankAtLeast (spanCodes [260, 148, 68, 52, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (148, 29), (68, 151), (52, 387), (8, 130), (2, 3), (1, 2)]
    (codeMat 241) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane315GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 160, 100, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (160, 224), (100, 119), (20, 31), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
