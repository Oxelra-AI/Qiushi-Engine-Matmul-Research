import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1140 :
    QuotientRankAtLeast (spanCodes [288, 129, 97, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 3), (129, 162), (97, 484), (17, 160), (8, 256), (4, 24), (2, 16)]
    (codeMat 142) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1141 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 22), (128, 1), (64, 2), (17, 80), (8, 128), (5, 32), (2, 8)]
    (codeMat 140) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1142 :
    QuotientRankAtLeast (spanCodes [289, 161, 65, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(289, 131), (161, 380), (65, 9), (17, 96), (8, 8), (5, 128), (2, 256)]
    (codeMat 87) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1143 :
    QuotientRankAtLeast (spanCodes [257, 161, 96, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 503), (161, 244), (96, 70), (16, 256), (9, 432), (5, 8), (3, 16)]
    (codeMat 142) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1144 :
    QuotientRankAtLeast (spanCodes [260, 129, 65, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(260, 4), (129, 129), (65, 3), (16, 8), (9, 216), (3, 128)]
    (codeMat 85) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1145 :
    QuotientRankAtLeast (spanCodes [256, 160, 97, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (160, 68), (97, 246), (16, 256), (9, 432), (5, 24), (3, 16)]
    (codeMat 142) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1146 :
    QuotientRankAtLeast (spanCodes [256, 161, 97, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (161, 244), (97, 246), (16, 256), (9, 432), (4, 24), (3, 16)]
    (codeMat 140) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1147 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (160, 68), (96, 70), (16, 256), (9, 432), (4, 8), (3, 16)]
    (codeMat 140) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1148 :
    QuotientRankAtLeast (spanCodes [260, 128, 65, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(260, 4), (128, 130), (65, 1), (17, 80), (8, 8), (2, 128)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1149 :
    QuotientRankAtLeast (spanCodes [288, 129, 97, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 384), (129, 21), (97, 413), (17, 149), (8, 360), (5, 3), (2, 2)]
    (codeMat 417) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
