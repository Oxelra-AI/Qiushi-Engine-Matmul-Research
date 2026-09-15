import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit197Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0060 :
    QuotientRankAtLeast (spanCodes [289, 67, 16, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(289, 129), (67, 269), (16, 32), (10, 268), (7, 390)]
    (codeMat 407) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane466GenSource0061 :
    QuotientRankAtLeast (spanCodes [292, 68, 21, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(292, 390), (68, 294), (21, 10), (8, 32), (2, 1)]
    (codeMat 401) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane466GenSource0062 :
    QuotientRankAtLeast (spanCodes [272, 68, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (68, 20), (32, 8), (8, 1), (2, 128), (1, 2)]
    (codeMat 266) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0063 :
    QuotientRankAtLeast (spanCodes [272, 64, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (64, 128), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0064 :
    QuotientRankAtLeast (spanCodes [274, 64, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 246), (64, 128), (34, 30), (10, 22), (4, 3), (1, 2)]
    (codeMat 273) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0065 :
    QuotientRankAtLeast (spanCodes [276, 68, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(276, 246), (68, 22), (36, 9), (8, 3), (2, 128), (1, 2)]
    (codeMat 267) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0066 :
    QuotientRankAtLeast (spanCodes [257, 68, 33, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(257, 490), (68, 175), (33, 42), (17, 10), (10, 11)]
    (codeMat 403) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane466GenSource0067 :
    QuotientRankAtLeast (spanCodes [256, 68, 49, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(256, 32), (68, 268), (49, 129), (9, 1), (3, 390)]
    (codeMat 163) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane466GenSource0068 :
    QuotientRankAtLeast (spanCodes [257, 68, 48, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(257, 300), (68, 268), (48, 128), (9, 1), (3, 390)]
    (codeMat 171) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane466GenSource0069 :
    QuotientRankAtLeast (spanCodes [256, 67, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(256, 1), (67, 42), (49, 422), (10, 170), (7, 32)]
    (codeMat 460) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
