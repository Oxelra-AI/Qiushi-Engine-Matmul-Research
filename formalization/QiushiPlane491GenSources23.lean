import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiWcOrbit220Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0230 :
    QuotientRankAtLeast (spanCodes [129, 68, 33, 16, 8, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 136), (68, 232), (33, 30), (16, 2), (8, 3), (3, 8)]
    (codeMat 330) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0231 :
    QuotientRankAtLeast (spanCodes [129, 68, 32, 16, 9, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 28), (68, 224), (32, 128), (16, 2), (9, 8), (2, 3)]
    (codeMat 275) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0232 :
    QuotientRankAtLeast (spanCodes [128, 68, 34, 16, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(128, 128), (68, 96), (34, 20), (16, 2), (8, 1), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0233 :
    QuotientRankAtLeast (spanCodes [134, 68, 36, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(134, 113), (68, 316), (36, 63), (16, 1), (14, 52), (1, 32)]
    (codeMat 394) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane491GenSource0234 :
    QuotientRankAtLeast (spanCodes [136, 68, 40, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(136, 20), (68, 104), (40, 128), (16, 2), (2, 1), (1, 8)]
    (codeMat 273) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0235 :
    QuotientRankAtLeast (spanCodes [146, 80, 49, 9, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(146, 1), (80, 42), (49, 160), (9, 32), (4, 438)]
    (codeMat 215) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0236 :
    QuotientRankAtLeast (spanCodes [139, 65, 40, 18, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(139, 10), (65, 16), (40, 325), (18, 1), (7, 256)]
    (codeMat 107) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane491GenSource0237 :
    QuotientRankAtLeast (spanCodes [132, 70, 38, 18, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(132, 232), (70, 96), (38, 30), (18, 3), (8, 9), (1, 8)]
    (codeMat 331) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0238 :
    QuotientRankAtLeast (spanCodes [129, 72, 34, 26, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(129, 414), (72, 192), (34, 52), (26, 53), (6, 16)]
    (codeMat 394) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane491GenSource0239 :
    QuotientRankAtLeast (spanCodes [146, 82, 49, 9, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(146, 27), (82, 11), (49, 324), (9, 1), (6, 256)]
    (codeMat 99) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

end QiushiMatmul
