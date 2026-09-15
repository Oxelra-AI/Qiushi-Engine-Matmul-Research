import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0170 :
    QuotientRankAtLeast (spanCodes [292, 162, 64, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(292, 216), (162, 208), (64, 5), (16, 128), (8, 2), (1, 4)]
    (codeMat 85) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0171 :
    QuotientRankAtLeast (spanCodes [288, 162, 66, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 3), (162, 484), (66, 162), (16, 256), (10, 160), (4, 24), (1, 16)]
    (codeMat 142) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0172 :
    QuotientRankAtLeast (spanCodes [288, 132, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (132, 168), (96, 69), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane480GenSource0173 :
    QuotientRankAtLeast (spanCodes [268, 140, 64, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(268, 272), (140, 273), (64, 2), (32, 32), (16, 40), (1, 130)]
    (codeMat 340) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0174 :
    QuotientRankAtLeast (spanCodes [260, 140, 72, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 9), (140, 313), (72, 128), (32, 8), (16, 40), (1, 130)]
    (codeMat 407) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0175 :
    QuotientRankAtLeast (spanCodes [260, 140, 64, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(260, 3), (140, 403), (64, 128), (40, 8), (16, 40), (1, 130)]
    (codeMat 277) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0176 :
    QuotientRankAtLeast (spanCodes [268, 140, 72, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(268, 11), (140, 443), (72, 128), (40, 8), (16, 40), (1, 130)]
    (codeMat 407) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0177 :
    QuotientRankAtLeast (spanCodes [256, 142, 72, 32, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 9), (142, 313), (72, 2), (32, 8), (16, 40), (1, 130)]
    (codeMat 470) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0178 :
    QuotientRankAtLeast (spanCodes [256, 142, 64, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(256, 3), (142, 403), (64, 2), (40, 8), (16, 40), (1, 130)]
    (codeMat 340) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane480GenSource0179 :
    QuotientRankAtLeast (spanCodes [264, 142, 72, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(264, 11), (142, 443), (72, 2), (40, 8), (16, 40), (1, 130)]
    (codeMat 470) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

end QiushiMatmul
