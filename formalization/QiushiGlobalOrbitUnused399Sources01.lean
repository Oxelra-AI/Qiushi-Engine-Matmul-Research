import QiushiGlobalOrbitUnused399Data
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono244From75
import QiushiStep128Mono246From75
import QiushiWcOrbit202Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane399UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [291, 164, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 162, 68, 20, 10] [(291, 90), (164, 68), (96, 495), (20, 259), (10, 248)]
    (codeMat 247) (codeMat 396) (codeMat 106) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit246_lb16_mono

theorem plane399UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [294, 164, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [133, 68, 35, 20, 10] [(294, 155), (164, 203), (96, 35), (20, 193), (10, 68)]
    (codeMat 98) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit244_lb16_mono

theorem plane399UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [295, 164, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 162, 68, 20, 10] [(295, 497), (164, 495), (96, 68), (20, 162), (10, 182)]
    (codeMat 158) (codeMat 470) (codeMat 213) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit246_lb16_mono

theorem plane399UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [164, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(164, 246), (96, 97), (20, 29), (8, 8), (2, 3), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane399UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [161, 96, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(161, 244), (96, 227), (17, 11), (9, 8), (5, 130), (3, 2)]
    (codeMat 395) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane399UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [259, 163, 96, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 8, 2, 1] [(259, 11), (163, 236), (96, 228), (19, 304), (10, 400), (7, 2)]
    (codeMat 141) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc202s9Dispatch

theorem plane399UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (64, 128), (32, 3), (20, 28), (10, 224)]
    (codeMat 102) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane399UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [259, 133, 65, 33, 20, 10]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 8, 2, 1] [(259, 71), (133, 68), (65, 2), (33, 383), (20, 228), (10, 402)]
    (codeMat 117) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc202s9Dispatch

theorem plane399UnusedGenSource0018 :
    QuotientRankAtLeast (spanCodes [261, 135, 67, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(261, 322), (135, 170), (67, 21), (35, 274), (20, 160), (10, 20)]
    (codeMat 143) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane399UnusedGenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 3), (68, 151), (36, 128), (20, 136), (10, 224)]
    (codeMat 212) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
