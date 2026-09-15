import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1570 :
    QuotientRankAtLeast (spanCodes [260, 129, 64, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (129, 137), (64, 219), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 87) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1571 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 70), (32, 8), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1572 :
    QuotientRankAtLeast (spanCodes [261, 129, 64, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(261, 228), (129, 137), (64, 219), (32, 32), (16, 8), (9, 216), (3, 128)]
    (codeMat 87) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1573 :
    QuotientRankAtLeast (spanCodes [289, 161, 97, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(289, 503), (161, 500), (97, 502), (16, 256), (9, 432), (5, 8), (3, 16)]
    (codeMat 140) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1574 :
    QuotientRankAtLeast (spanCodes [256, 160, 65, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (160, 149), (65, 9), (16, 360), (9, 8), (5, 384), (3, 256)]
    (codeMat 94) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1575 :
    QuotientRankAtLeast (spanCodes [288, 129, 64, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(288, 54), (129, 138), (64, 219), (16, 128), (9, 216), (5, 40), (3, 8)]
    (codeMat 143) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1576 :
    QuotientRankAtLeast (spanCodes [385, 64, 32, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(385, 80), (64, 128), (32, 54), (16, 63), (9, 2), (5, 32), (3, 40)]
    (codeMat 267) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1577 :
    QuotientRankAtLeast (spanCodes [289, 128, 65, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 28), (128, 130), (65, 219), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 142) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1578 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (160, 149), (64, 1), (16, 360), (9, 8), (4, 128), (3, 256)]
    (codeMat 92) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1579 :
    QuotientRankAtLeast (spanCodes [320, 129, 33, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(320, 128), (129, 240), (33, 52), (16, 3), (9, 54), (4, 32), (3, 40)]
    (codeMat 266) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
