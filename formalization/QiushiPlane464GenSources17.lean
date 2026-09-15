import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0170 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 33, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (128, 1), (68, 31), (33, 227), (21, 105), (8, 511), (2, 8)]
    (codeMat 460) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0171 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 20), (129, 21), (64, 2), (49, 80), (8, 128), (4, 32), (2, 40)]
    (codeMat 140) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane464GenSource0172 :
    QuotientRankAtLeast (spanCodes [273, 145, 64, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 116), (145, 118), (64, 1), (33, 96), (8, 8), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0173 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 33, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 119), (128, 360), (68, 126), (33, 503), (21, 105), (9, 511), (3, 130)]
    (codeMat 407) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0174 :
    QuotientRankAtLeast (spanCodes [273, 144, 64, 32, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 407), (144, 511), (64, 8), (32, 130), (9, 1), (4, 128), (3, 384)]
    (codeMat 99) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0175 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 32, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 224), (130, 128), (66, 488), (32, 3), (16, 2), (10, 23), (6, 8)]
    (codeMat 330) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0176 :
    QuotientRankAtLeast (spanCodes [258, 129, 64, 34, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 278), (129, 245), (64, 360), (34, 276), (19, 373), (10, 235), (4, 130)]
    (codeMat 478) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0177 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (130, 2), (64, 325), (34, 160), (16, 16), (10, 168), (4, 256)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane464GenSource0178 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 96), (128, 128), (64, 384), (32, 1), (16, 2), (10, 22), (4, 8)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane464GenSource0179 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 224), (129, 232), (68, 480), (32, 511), (21, 150), (9, 3), (3, 360)]
    (codeMat 355) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
