import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0160 :
    QuotientRankAtLeast (spanCodes [263, 131, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 31), (131, 224), (68, 252), (36, 9), (17, 96), (10, 104)]
    (codeMat 123) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0161 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (132, 68), (68, 70), (36, 8), (17, 160), (10, 176)]
    (codeMat 92) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane486GenSource0162 :
    QuotientRankAtLeast (spanCodes [259, 135, 68, 36, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 136), (135, 104), (68, 232), (36, 3), (17, 148), (10, 150)]
    (codeMat 355) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0163 :
    QuotientRankAtLeast (spanCodes [259, 132, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 31), (132, 252), (68, 255), (39, 22), (17, 148), (10, 150)]
    (codeMat 95) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0164 :
    QuotientRankAtLeast (spanCodes [259, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 224), (130, 3), (68, 255), (32, 128), (16, 2), (10, 150)]
    (codeMat 87) (codeMat 331) (codeMat 410) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0165 :
    QuotientRankAtLeast (spanCodes [259, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 104), (128, 128), (68, 224), (34, 148), (16, 2), (10, 151)]
    (codeMat 298) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0166 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(257, 68), (130, 2), (68, 69), (34, 160), (16, 16), (10, 168)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane486GenSource0167 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (135, 22), (68, 150), (34, 252), (21, 31), (10, 255)]
    (codeMat 111) (codeMat 379) (codeMat 247) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0168 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 35, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (132, 96), (68, 105), (35, 28), (22, 224), (10, 255)]
    (codeMat 124) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane486GenSource0169 :
    QuotientRankAtLeast (spanCodes [256, 131, 68, 36, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 9), (131, 252), (68, 119), (36, 8), (22, 104), (10, 224)]
    (codeMat 159) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
