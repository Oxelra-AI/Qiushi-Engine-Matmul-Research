import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiOrbit40FP
import QiushiOrbit41FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0140 :
    QuotientRankAtLeast (spanCodes [256, 84, 48, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(256, 384), (84, 116), (48, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane425GenSource0141 :
    QuotientRankAtLeast (spanCodes [256, 84, 36, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 128] [(256, 128), (84, 116), (36, 2), (8, 9), (2, 32), (1, 8)]
    (codeMat 267) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit40_lb12

theorem plane425GenSource0142 :
    QuotientRankAtLeast (spanCodes [256, 148, 84, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 128] [(256, 32), (148, 220), (84, 212), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit40_lb12

theorem plane425GenSource0143 :
    QuotientRankAtLeast (spanCodes [256, 132, 84, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 384] [(256, 384), (132, 118), (84, 84), (8, 32), (2, 9), (1, 8)]
    (codeMat 177) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit41_lb12

theorem plane425GenSource0144 :
    QuotientRankAtLeast (spanCodes [256, 128, 84, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84, 128] [(256, 32), (128, 8), (84, 84), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit40_lb12

theorem plane425GenSource0145 :
    QuotientRankAtLeast (spanCodes [256, 164, 100, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (164, 246), (100, 118), (20, 30), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0146 :
    QuotientRankAtLeast (spanCodes [256, 148, 68, 48, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (148, 29), (68, 149), (48, 384), (8, 128), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0147 :
    QuotientRankAtLeast (spanCodes [256, 144, 68, 52, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (144, 8), (68, 149), (52, 385), (8, 130), (2, 1), (1, 2)]
    (codeMat 241) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0148 :
    QuotientRankAtLeast (spanCodes [256, 132, 80, 52, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (132, 96), (80, 404), (52, 257), (8, 130), (2, 256), (1, 128)]
    (codeMat 107) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane425GenSource0149 :
    QuotientRankAtLeast (spanCodes [258, 128, 82, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 118), (128, 511), (82, 284), (50, 392), (10, 224), (4, 384), (1, 256)]
    (codeMat 94) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
