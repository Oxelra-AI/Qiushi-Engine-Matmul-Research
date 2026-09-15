import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0230 :
    QuotientRankAtLeast (spanCodes [132, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 133), (64, 40), (20, 132), (8, 32), (2, 2)]
    (codeMat 142) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0231 :
    QuotientRankAtLeast (spanCodes [133, 65, 21, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(133, 135), (65, 40), (21, 132), (8, 32), (2, 2)]
    (codeMat 143) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0232 :
    QuotientRankAtLeast (spanCodes [128, 69, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 32), (69, 166), (17, 10), (9, 9), (3, 2)]
    (codeMat 267) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0233 :
    QuotientRankAtLeast (spanCodes [133, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(133, 173), (64, 40), (20, 166), (9, 32), (3, 2)]
    (codeMat 207) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0234 :
    QuotientRankAtLeast (spanCodes [129, 69, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(129, 34), (69, 164), (17, 10), (9, 9), (3, 2)]
    (codeMat 331) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0235 :
    QuotientRankAtLeast (spanCodes [133, 65, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(133, 175), (65, 40), (21, 166), (9, 32), (3, 2)]
    (codeMat 206) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0236 :
    QuotientRankAtLeast (spanCodes [144, 84, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(144, 2), (84, 116), (8, 32), (2, 1), (1, 8)]
    (codeMat 177) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane487GenSource0237 :
    QuotientRankAtLeast (spanCodes [128, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 1), (64, 8), (20, 132), (8, 32), (2, 2)]
    (codeMat 140) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0238 :
    QuotientRankAtLeast (spanCodes [132, 68, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 132), (68, 164), (16, 1), (8, 9), (2, 2)]
    (codeMat 266) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane487GenSource0239 :
    QuotientRankAtLeast (spanCodes [129, 65, 21, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(129, 11), (65, 8), (21, 166), (9, 32), (3, 2)]
    (codeMat 205) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
