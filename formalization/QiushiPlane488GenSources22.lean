import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0220 :
    QuotientRankAtLeast (spanCodes [257, 135, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 232), (135, 224), (71, 96), (39, 150), (17, 151), (10, 149)]
    (codeMat 299) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0221 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 3), (68, 150), (36, 128), (20, 136), (10, 232)]
    (codeMat 212) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0222 :
    QuotientRankAtLeast (spanCodes [262, 134, 70, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 20), (134, 22), (70, 148), (38, 28), (22, 31), (10, 252)]
    (codeMat 102) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0223 :
    QuotientRankAtLeast (spanCodes [258, 132, 65, 33, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 148), (132, 150), (65, 130), (33, 252), (23, 255), (10, 227)]
    (codeMat 110) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0224 :
    QuotientRankAtLeast (spanCodes [263, 131, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 31), (131, 224), (68, 252), (36, 9), (17, 96), (10, 104)]
    (codeMat 123) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0225 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (132, 68), (68, 70), (36, 8), (17, 160), (10, 176)]
    (codeMat 92) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane488GenSource0226 :
    QuotientRankAtLeast (spanCodes [259, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 136), (135, 104), (68, 232), (36, 3), (17, 148), (10, 150)]
    (codeMat 355) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0227 :
    QuotientRankAtLeast (spanCodes [256, 135, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 9), (135, 104), (71, 105), (39, 22), (17, 148), (10, 150)]
    (codeMat 92) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0228 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 128), (68, 150), (36, 3), (21, 224), (10, 255)]
    (codeMat 103) (codeMat 205) (codeMat 242) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0229 :
    QuotientRankAtLeast (spanCodes [256, 131, 68, 36, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 9), (131, 252), (68, 119), (36, 8), (22, 104), (10, 224)]
    (codeMat 159) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
