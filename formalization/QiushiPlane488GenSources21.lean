import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiOrbit29FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0210 :
    QuotientRankAtLeast (spanCodes [400, 80, 48, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(400, 104), (80, 232), (48, 8), (10, 29), (6, 1), (1, 3)]
    (codeMat 273) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0211 :
    QuotientRankAtLeast (spanCodes [256, 162, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (162, 148), (96, 28), (10, 104), (4, 1), (1, 8)]
    (codeMat 169) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0212 :
    QuotientRankAtLeast (spanCodes [272, 144, 80, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(272, 10), (144, 2), (80, 34), (48, 9), (10, 164)]
    (codeMat 230) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0213 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(288, 2), (128, 8), (96, 34), (16, 9), (10, 118)]
    (codeMat 102) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane488GenSource0214 :
    QuotientRankAtLeast (spanCodes [384, 64, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(384, 8), (64, 32), (32, 3), (16, 2), (10, 132)]
    (codeMat 98) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0215 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 22), (134, 20), (64, 128), (32, 9), (16, 8), (10, 96)]
    (codeMat 98) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0216 :
    QuotientRankAtLeast (spanCodes [386, 66, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(386, 164), (66, 173), (34, 134), (16, 2), (10, 133)]
    (codeMat 114) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0217 :
    QuotientRankAtLeast (spanCodes [261, 135, 66, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 252), (135, 28), (66, 227), (34, 104), (16, 8), (10, 97)]
    (codeMat 114) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0218 :
    QuotientRankAtLeast (spanCodes [260, 130, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (130, 130), (71, 150), (39, 96), (17, 97), (10, 105)]
    (codeMat 107) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0219 :
    QuotientRankAtLeast (spanCodes [258, 132, 71, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(258, 68), (132, 69), (71, 71), (39, 160), (17, 168), (10, 184)]
    (codeMat 93) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
