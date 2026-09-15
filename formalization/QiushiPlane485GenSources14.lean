import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit95From31
import QiushiOrbit31FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0140 :
    QuotientRankAtLeast (spanCodes [33, 16, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0141 :
    QuotientRankAtLeast (spanCodes [32, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0142 :
    QuotientRankAtLeast (spanCodes [34, 16, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(34, 20), (16, 2), (10, 21), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0143 :
    QuotientRankAtLeast (spanCodes [36, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(36, 54), (20, 52), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane485GenSource0144 :
    QuotientRankAtLeast (spanCodes [68, 32, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(68, 80), (32, 2), (20, 20), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0145 :
    QuotientRankAtLeast (spanCodes [129, 33, 16, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(129, 80), (33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0146 :
    QuotientRankAtLeast (spanCodes [128, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 1), (64, 8), (20, 132), (8, 32), (2, 2)]
    (codeMat 140) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0147 :
    QuotientRankAtLeast (spanCodes [129, 65, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(129, 11), (65, 8), (20, 166), (9, 32), (3, 2)]
    (codeMat 205) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0148 :
    QuotientRankAtLeast (spanCodes [128, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 9), (64, 8), (20, 166), (9, 32), (3, 2)]
    (codeMat 204) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0149 :
    QuotientRankAtLeast (spanCodes [128, 65, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 3), (65, 8), (20, 132), (8, 32), (2, 2)]
    (codeMat 141) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
