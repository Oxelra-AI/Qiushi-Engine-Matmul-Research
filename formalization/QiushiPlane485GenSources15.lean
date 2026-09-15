import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit31FP
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0150 :
    QuotientRankAtLeast (spanCodes [132, 68, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(132, 82), (68, 80), (20, 100), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0151 :
    QuotientRankAtLeast (spanCodes [132, 64, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 133), (64, 40), (20, 132), (8, 32), (2, 2)]
    (codeMat 142) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0152 :
    QuotientRankAtLeast (spanCodes [133, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(133, 173), (64, 40), (20, 166), (9, 32), (3, 2)]
    (codeMat 207) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0153 :
    QuotientRankAtLeast (spanCodes [132, 65, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 175), (65, 40), (20, 166), (9, 32), (3, 2)]
    (codeMat 206) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0154 :
    QuotientRankAtLeast (spanCodes [132, 65, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(132, 135), (65, 40), (20, 132), (8, 32), (2, 2)]
    (codeMat 143) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane485GenSource0155 :
    QuotientRankAtLeast (spanCodes [128, 68, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(128, 2), (68, 80), (20, 68), (8, 32), (2, 1), (1, 8)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0156 :
    QuotientRankAtLeast (spanCodes [193, 32, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(193, 120), (32, 2), (17, 62), (9, 63), (5, 40), (3, 8)]
    (codeMat 266) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane485GenSource0157 :
    QuotientRankAtLeast (spanCodes [260, 64, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(260, 192), (64, 16), (38, 427), (20, 245), (10, 378)]
    (codeMat 358) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane485GenSource0158 :
    QuotientRankAtLeast (spanCodes [291, 65, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(291, 37), (65, 192), (19, 427), (10, 245), (7, 36)]
    (codeMat 375) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane485GenSource0159 :
    QuotientRankAtLeast (spanCodes [258, 66, 38, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(258, 414), (66, 398), (38, 350), (20, 245), (10, 399)]
    (codeMat 486) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

end QiushiMatmul
