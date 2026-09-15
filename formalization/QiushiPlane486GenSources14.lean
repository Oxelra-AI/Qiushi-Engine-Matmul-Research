import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0140 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (129, 30), (64, 3), (35, 96), (10, 232), (4, 8)]
    (codeMat 204) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0141 :
    QuotientRankAtLeast (spanCodes [256, 131, 64, 33, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (131, 139), (64, 9), (33, 31), (10, 252), (4, 3)]
    (codeMat 172) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0142 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 11), (129, 139), (65, 9), (35, 227), (10, 252), (5, 3)]
    (codeMat 165) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0143 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 10), (128, 128), (65, 8), (35, 252), (10, 224), (5, 3)]
    (codeMat 165) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0144 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 34, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (129, 28), (64, 3), (34, 96), (10, 224), (4, 8)]
    (codeMat 140) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0145 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 33, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (130, 128), (64, 8), (33, 28), (10, 224), (4, 3)]
    (codeMat 172) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0146 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane486GenSource0147 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 136), (130, 128), (68, 232), (32, 3), (16, 2), (10, 150)]
    (codeMat 354) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0148 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 31), (134, 28), (68, 252), (32, 9), (16, 8), (10, 104)]
    (codeMat 114) (codeMat 124) (codeMat 124) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0149 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 31), (128, 3), (68, 252), (34, 22), (16, 2), (10, 148)]
    (codeMat 86) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
