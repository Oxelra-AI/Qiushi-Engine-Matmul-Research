import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0590 :
    QuotientRankAtLeast (spanCodes [256, 130, 65, 33, 18, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (130, 2), (65, 3), (33, 424), (18, 16), (9, 24), (7, 256)]
    (codeMat 93) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0591 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 32, 18, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 381), (131, 406), (65, 130), (32, 360), (18, 384), (9, 128), (7, 8)]
    (codeMat 206) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0592 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 33, 16, 8, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 363), (130, 2), (67, 148), (33, 480), (16, 128), (8, 256), (7, 360)]
    (codeMat 157) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0593 :
    QuotientRankAtLeast (spanCodes [257, 130, 65, 33, 18, 8, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 361), (130, 2), (65, 1), (33, 105), (18, 130), (8, 8), (7, 511)]
    (codeMat 405) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0594 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 35, 18, 11, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (128, 2), (65, 325), (35, 280), (18, 16), (11, 168), (7, 256)]
    (codeMat 92) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0595 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (131, 28), (67, 31), (32, 128), (16, 256), (10, 480), (7, 8)]
    (codeMat 140) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0596 :
    QuotientRankAtLeast (spanCodes [256, 130, 65, 33, 19, 9, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (130, 256), (65, 128), (33, 381), (19, 276), (9, 130), (6, 8)]
    (codeMat 334) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0597 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 35, 18, 9, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 71), (128, 3), (64, 2), (35, 440), (18, 24), (9, 16), (6, 256)]
    (codeMat 92) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0598 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 34, 18, 8, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 373), (129, 97), (64, 8), (34, 258), (18, 256), (8, 1), (6, 130)]
    (codeMat 226) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0599 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 34, 16, 11, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (129, 70), (66, 71), (34, 272), (16, 432), (11, 440), (6, 256)]
    (codeMat 93) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
