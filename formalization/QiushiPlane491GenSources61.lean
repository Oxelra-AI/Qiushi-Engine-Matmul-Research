import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0610 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 35, 19, 9, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 240), (128, 32), (65, 216), (35, 70), (19, 196), (9, 3), (6, 128)]
    (codeMat 99) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0611 :
    QuotientRankAtLeast (spanCodes [257, 130, 65, 33, 18, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 240), (130, 8), (65, 40), (33, 198), (18, 1), (11, 69), (7, 128)]
    (codeMat 107) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0612 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 32, 16, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 404), (131, 126), (67, 119), (32, 256), (16, 384), (11, 392), (7, 360)]
    (codeMat 159) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0613 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 32, 18, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 29), (131, 22), (65, 2), (32, 360), (18, 384), (9, 128), (7, 8)]
    (codeMat 205) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0614 :
    QuotientRankAtLeast (spanCodes [258, 131, 66, 32, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 276), (131, 373), (66, 235), (32, 2), (18, 384), (10, 387), (4, 130)]
    (codeMat 234) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0615 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 32, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 104), (131, 480), (65, 256), (32, 9), (17, 31), (10, 28), (4, 8)]
    (codeMat 331) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0616 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 35, 16, 8, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (128, 3), (64, 1), (35, 160), (16, 24), (8, 8), (4, 256)]
    (codeMat 84) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0617 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 33, 16, 8, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 284), (130, 8), (64, 130), (33, 149), (16, 1), (8, 2), (4, 511)]
    (codeMat 426) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0618 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 33, 17, 8, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 264), (130, 256), (65, 128), (33, 149), (17, 148), (8, 2), (4, 360)]
    (codeMat 354) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0619 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 33, 17, 9, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 509), (130, 3), (65, 1), (33, 264), (17, 136), (9, 8), (4, 360)]
    (codeMat 157) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
