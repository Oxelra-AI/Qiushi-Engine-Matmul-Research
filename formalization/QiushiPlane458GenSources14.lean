import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0140 :
    QuotientRankAtLeast (spanCodes [388, 68, 36, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(388, 240), (68, 112), (36, 54), (20, 53), (8, 1), (2, 40), (1, 8)]
    (codeMat 266) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0141 :
    QuotientRankAtLeast (spanCodes [388, 68, 32, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(388, 240), (68, 112), (32, 54), (20, 29), (8, 9), (2, 40), (1, 8)]
    (codeMat 267) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0142 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (132, 28), (68, 20), (20, 196), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0143 :
    QuotientRankAtLeast (spanCodes [256, 161, 96, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (161, 116), (96, 97), (16, 511), (9, 360), (4, 1), (3, 2)]
    (codeMat 481) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0144 :
    QuotientRankAtLeast (spanCodes [256, 160, 97, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (160, 227), (97, 119), (17, 258), (9, 384), (5, 1), (3, 2)]
    (codeMat 241) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0145 :
    QuotientRankAtLeast (spanCodes [256, 161, 96, 17, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (161, 117), (96, 227), (17, 386), (9, 256), (5, 3), (3, 2)]
    (codeMat 241) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0146 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 60), (129, 10), (65, 3), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 141) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0147 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (128, 8), (68, 22), (20, 70), (8, 128), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0148 :
    QuotientRankAtLeast (spanCodes [260, 164, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (164, 246), (96, 97), (20, 29), (8, 8), (2, 3), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0149 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (132, 82), (68, 100), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 86) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
