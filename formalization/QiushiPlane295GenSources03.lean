import QiushiPlane295GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane295GenSource0030 :
    QuotientRankAtLeast (spanCodes [262, 134, 66, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 126), (134, 119), (66, 404), (32, 511), (22, 503), (10, 276), (1, 130)]
    (codeMat 415) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0031 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (134, 20), (64, 9), (32, 130), (20, 276), (10, 97), (1, 8)]
    (codeMat 461) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0032 :
    QuotientRankAtLeast (spanCodes [260, 130, 66, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (130, 256), (66, 104), (32, 130), (20, 276), (10, 97), (1, 8)]
    (codeMat 335) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0033 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane295GenSource0034 :
    QuotientRankAtLeast (spanCodes [256, 130, 70, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (130, 130), (70, 227), (32, 1), (16, 2), (10, 149), (1, 511)]
    (codeMat 482) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0035 :
    QuotientRankAtLeast (spanCodes [258, 192, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 240), (192, 128), (32, 3), (18, 54), (10, 52), (6, 40), (1, 32)]
    (codeMat 266) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane295GenSource0036 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (134, 150), (68, 362), (32, 130), (20, 406), (10, 227), (1, 511)]
    (codeMat 477) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0037 :
    QuotientRankAtLeast (spanCodes [258, 134, 66, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 414), (134, 373), (66, 97), (32, 384), (18, 360), (10, 104), (1, 8)]
    (codeMat 143) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 30), (132, 29), (64, 9), (32, 384), (18, 360), (10, 104), (1, 8)]
    (codeMat 141) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane295GenSource0039 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (128, 2), (70, 68), (32, 24), (16, 16), (10, 160), (1, 256)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
