import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0160 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 255), (130, 384), (67, 246), (34, 406), (19, 235), (10, 414), (7, 511)]
    (codeMat 342) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0161 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 35, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 258), (130, 1), (67, 71), (35, 272), (18, 8), (10, 440), (7, 256)]
    (codeMat 93) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane464GenSource0162 :
    QuotientRankAtLeast (spanCodes [258, 131, 66, 32, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 139), (131, 287), (66, 483), (32, 8), (17, 284), (10, 227), (6, 130)]
    (codeMat 407) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0163 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 32, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 227), (130, 130), (66, 381), (32, 3), (16, 2), (10, 21), (6, 8)]
    (codeMat 458) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0164 :
    QuotientRankAtLeast (spanCodes [257, 128, 66, 34, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 97), (128, 130), (66, 406), (34, 151), (16, 2), (10, 150), (6, 511)]
    (codeMat 426) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0165 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 34, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 138), (129, 406), (66, 276), (34, 508), (17, 150), (10, 148), (6, 511)]
    (codeMat 419) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0166 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 34, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 413), (128, 360), (67, 353), (34, 414), (17, 105), (10, 97), (7, 130)]
    (codeMat 478) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0167 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 219), (132, 210), (68, 228), (36, 216), (20, 208), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane464GenSource0168 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane464GenSource0169 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (132, 509), (68, 510), (37, 392), (21, 264), (8, 384), (2, 360)]
    (codeMat 156) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
