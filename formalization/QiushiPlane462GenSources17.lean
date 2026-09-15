import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0170 :
    QuotientRankAtLeast (spanCodes [256, 160, 65, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (160, 413), (65, 8), (17, 131), (9, 1), (5, 256), (3, 128)]
    (codeMat 107) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0171 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 17, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 96), (160, 284), (64, 8), (17, 131), (9, 1), (4, 256), (3, 128)]
    (codeMat 99) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0172 :
    QuotientRankAtLeast (spanCodes [256, 160, 65, 16, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (160, 149), (65, 8), (16, 2), (8, 1), (5, 256), (2, 128)]
    (codeMat 106) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0173 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 16, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 96), (160, 20), (64, 8), (16, 2), (8, 1), (4, 256), (2, 128)]
    (codeMat 98) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0174 :
    QuotientRankAtLeast (spanCodes [258, 160, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 503), (160, 70), (66, 178), (18, 432), (10, 176), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane462GenSource0175 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (160, 70), (64, 2), (18, 432), (10, 176), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane462GenSource0176 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (160, 70), (68, 176), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane462GenSource0177 :
    QuotientRankAtLeast (spanCodes [276, 132, 68, 52, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 252), (132, 31), (68, 23), (52, 259), (8, 130), (2, 3), (1, 2)]
    (codeMat 225) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0178 :
    QuotientRankAtLeast (spanCodes [258, 144, 64, 34, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 76), (144, 32), (64, 216), (34, 68), (10, 196), (4, 1), (1, 3)]
    (codeMat 177) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0179 :
    QuotientRankAtLeast (spanCodes [274, 128, 64, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(274, 502), (128, 384), (64, 128), (50, 510), (10, 150), (4, 1), (1, 2)]
    (codeMat 305) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
