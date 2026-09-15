import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep128Mono190From72
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0220 :
    QuotientRankAtLeast (spanCodes [160, 64, 20, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 224), (64, 128), (20, 28), (12, 20), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0221 :
    QuotientRankAtLeast (spanCodes [162, 66, 16, 8, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(162, 126), (66, 22), (16, 9), (8, 1), (6, 130), (1, 2)]
    (codeMat 266) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0222 :
    QuotientRankAtLeast (spanCodes [162, 66, 18, 8, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(162, 246), (66, 22), (18, 9), (8, 3), (4, 128), (1, 2)]
    (codeMat 267) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0223 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 104), (68, 148), (16, 8), (12, 20), (2, 1), (1, 2)]
    (codeMat 401) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0224 :
    QuotientRankAtLeast (spanCodes [133, 65, 37, 21, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(133, 170), (65, 438), (37, 43), (21, 42), (3, 32)]
    (codeMat 394) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0225 :
    QuotientRankAtLeast (spanCodes [141, 73, 45, 29, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(141, 85), (73, 27), (45, 325), (29, 69), (3, 1)]
    (codeMat 177) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane491GenSource0226 :
    QuotientRankAtLeast (spanCodes [139, 72, 40, 26, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(139, 129), (72, 1), (40, 438), (26, 138), (6, 32)]
    (codeMat 334) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0227 :
    QuotientRankAtLeast (spanCodes [138, 73, 41, 26, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(138, 193), (73, 1), (41, 399), (26, 209), (7, 36)]
    (codeMat 375) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane491GenSource0228 :
    QuotientRankAtLeast (spanCodes [138, 72, 41, 25, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 128, 32, 10, 1] [(138, 495), (72, 128), (41, 10), (25, 42), (5, 1)]
    (codeMat 401) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit190_lb15_mono

theorem plane491GenSource0229 :
    QuotientRankAtLeast (spanCodes [138, 75, 41, 24, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(138, 33), (75, 11), (41, 278), (24, 32), (7, 128)]
    (codeMat 143) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
