import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0510 :
    QuotientRankAtLeast (spanCodes [264, 130, 72, 32, 26, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 324), (130, 511), (72, 1), (32, 256), (26, 440), (6, 24), (1, 8)]
    (codeMat 142) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0511 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 32, 17, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 22), (129, 30), (65, 54), (32, 128), (17, 198), (4, 2), (2, 3)]
    (codeMat 161) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0512 :
    QuotientRankAtLeast (spanCodes [264, 129, 72, 32, 24, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 151), (129, 224), (72, 511), (32, 2), (24, 3), (4, 128), (2, 256)]
    (codeMat 106) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0513 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 17, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 43), (128, 9), (64, 54), (33, 240), (17, 112), (5, 40), (2, 8)]
    (codeMat 141) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0514 :
    QuotientRankAtLeast (spanCodes [265, 128, 72, 33, 25, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(265, 480), (128, 8), (72, 511), (33, 259), (25, 385), (5, 3), (2, 1)]
    (codeMat 225) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0515 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (129, 34), (64, 54), (33, 112), (16, 128), (4, 8), (3, 32)]
    (codeMat 141) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0516 :
    QuotientRankAtLeast (spanCodes [264, 136, 65, 40, 17, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 259), (136, 70), (65, 511), (40, 256), (17, 440), (4, 24), (3, 8)]
    (codeMat 142) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0517 :
    QuotientRankAtLeast (spanCodes [265, 128, 72, 32, 24, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(265, 237), (128, 256), (72, 325), (32, 3), (24, 1), (4, 24), (3, 8)]
    (codeMat 266) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0518 :
    QuotientRankAtLeast (spanCodes [256, 136, 73, 40, 24, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (136, 327), (73, 511), (40, 3), (24, 2), (5, 24), (3, 16)]
    (codeMat 266) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0519 :
    QuotientRankAtLeast (spanCodes [264, 129, 72, 33, 25, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 381), (129, 259), (72, 511), (33, 488), (25, 480), (5, 128), (3, 256)]
    (codeMat 85) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
