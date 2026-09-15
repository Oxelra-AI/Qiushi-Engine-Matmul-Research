import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0290 :
    QuotientRankAtLeast (spanCodes [272, 144, 80, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 488), (144, 360), (80, 232), (50, 21), (10, 29), (6, 2), (1, 3)]
    (codeMat 273) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0291 :
    QuotientRankAtLeast (spanCodes [272, 146, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 406), (146, 256), (82, 255), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 465) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0292 :
    QuotientRankAtLeast (spanCodes [272, 128, 82, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 149), (128, 511), (82, 284), (32, 360), (10, 224), (6, 128), (1, 256)]
    (codeMat 94) (codeMat 470) (codeMat 213) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0293 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 29), (128, 3), (80, 28), (34, 232), (10, 224), (6, 384), (1, 256)]
    (codeMat 84) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0294 :
    QuotientRankAtLeast (spanCodes [272, 144, 64, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 326), (144, 325), (64, 2), (34, 424), (10, 168), (6, 24), (1, 16)]
    (codeMat 140) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane426GenSource0295 :
    QuotientRankAtLeast (spanCodes [256, 160, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (160, 68), (66, 162), (16, 256), (10, 160), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane426GenSource0296 :
    QuotientRankAtLeast (spanCodes [258, 192, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 240), (192, 128), (32, 3), (18, 54), (10, 52), (6, 40), (1, 32)]
    (codeMat 266) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0297 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 265), (128, 256), (70, 393), (38, 97), (22, 105), (10, 284), (1, 511)]
    (codeMat 279) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0298 :
    QuotientRankAtLeast (spanCodes [262, 132, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 287), (132, 483), (66, 404), (38, 284), (22, 227), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0299 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 22), (134, 20), (64, 1), (38, 406), (22, 276), (10, 97), (1, 8)]
    (codeMat 396) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
