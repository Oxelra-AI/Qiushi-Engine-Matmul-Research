import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit93From29
import QiushiOrbit31FP
import QiushiPlane278GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0150 :
    QuotientRankAtLeast (spanCodes [384, 86, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(384, 1), (86, 99), (54, 2), (10, 306)]
    (codeMat 156) (codeMat 115) (codeMat 492) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0151 :
    QuotientRankAtLeast (spanCodes [432, 96, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(432, 2), (96, 304), (10, 97), (6, 1)]
    (codeMat 177) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane488GenSource0152 :
    QuotientRankAtLeast (spanCodes [96, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 8, 2, 1] [(96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit93_lb15_mono

theorem plane488GenSource0153 :
    QuotientRankAtLeast (spanCodes [96, 17, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(96, 164), (17, 11), (9, 2), (4, 32), (3, 8)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0154 :
    QuotientRankAtLeast (spanCodes [96, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(96, 166), (17, 11), (9, 2), (5, 32), (3, 8)]
    (codeMat 331) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0155 :
    QuotientRankAtLeast (spanCodes [96, 16, 8, 5, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(96, 134), (16, 1), (8, 2), (5, 32), (2, 8)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0156 :
    QuotientRankAtLeast (spanCodes [68, 36, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(68, 112), (36, 54), (20, 52), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane488GenSource0157 :
    QuotientRankAtLeast (spanCodes [68, 36, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(68, 164), (36, 32), (16, 1), (8, 2), (2, 9)]
    (codeMat 282) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0158 :
    QuotientRankAtLeast (spanCodes [80, 48, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(80, 133), (48, 1), (8, 2), (4, 32), (2, 40)]
    (codeMat 266) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0159 :
    QuotientRankAtLeast (spanCodes [81, 49, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(81, 175), (49, 11), (9, 2), (4, 32), (3, 40)]
    (codeMat 267) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
