import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiOrbit31FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0180 :
    QuotientRankAtLeast (spanCodes [129, 69, 37, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 136), (69, 224), (37, 28), (17, 10), (9, 3), (3, 8)]
    (codeMat 331) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0181 :
    QuotientRankAtLeast (spanCodes [161, 96, 17, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(161, 244), (96, 224), (17, 11), (9, 8), (4, 128), (3, 2)]
    (codeMat 267) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0182 :
    QuotientRankAtLeast (spanCodes [160, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 224), (96, 96), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0183 :
    QuotientRankAtLeast (spanCodes [259, 67, 35, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(259, 135), (67, 175), (35, 132), (10, 166), (4, 2)]
    (codeMat 207) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0184 :
    QuotientRankAtLeast (spanCodes [257, 65, 33, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 10), (65, 9), (33, 34), (10, 166), (5, 2)]
    (codeMat 205) (codeMat 185) (codeMat 481) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0185 :
    QuotientRankAtLeast (spanCodes [256, 64, 32, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(256, 8), (64, 9), (32, 32), (10, 164), (5, 2)]
    (codeMat 140) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0186 :
    QuotientRankAtLeast (spanCodes [260, 64, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(260, 8), (64, 3), (32, 32), (10, 132), (1, 2)]
    (codeMat 141) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0187 :
    QuotientRankAtLeast (spanCodes [262, 66, 34, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(262, 173), (66, 135), (34, 164), (10, 132), (1, 2)]
    (codeMat 143) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0188 :
    QuotientRankAtLeast (spanCodes [288, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(288, 2), (96, 34), (10, 118), (4, 1), (1, 9)]
    (codeMat 305) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane488GenSource0189 :
    QuotientRankAtLeast (spanCodes [256, 66, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(256, 2), (66, 82), (34, 68), (10, 100), (4, 1), (1, 9)]
    (codeMat 161) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
