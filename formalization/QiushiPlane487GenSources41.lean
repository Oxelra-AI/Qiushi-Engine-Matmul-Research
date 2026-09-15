import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit55Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0410 :
    QuotientRankAtLeast (spanCodes [293, 133, 64, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(293, 22), (133, 227), (64, 130), (20, 232), (9, 128), (3, 8)]
    (codeMat 207) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0411 :
    QuotientRankAtLeast (spanCodes [385, 81, 48, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(385, 20), (81, 235), (48, 3), (9, 8), (5, 128), (3, 130)]
    (codeMat 267) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0412 :
    QuotientRankAtLeast (spanCodes [293, 133, 65, 21, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(293, 22), (133, 105), (65, 130), (21, 96), (8, 128), (2, 8)]
    (codeMat 143) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0413 :
    QuotientRankAtLeast (spanCodes [385, 80, 48, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(385, 20), (80, 97), (48, 1), (8, 8), (4, 128), (2, 130)]
    (codeMat 266) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0414 :
    QuotientRankAtLeast (spanCodes [294, 134, 66, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(294, 136), (134, 232), (66, 29), (22, 224), (10, 28), (1, 3)]
    (codeMat 190) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0415 :
    QuotientRankAtLeast (spanCodes [386, 82, 50, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(386, 148), (82, 252), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 401) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane487GenSource0416 :
    QuotientRankAtLeast (spanCodes [130, 67, 35, 18, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(130, 1), (67, 15), (35, 304), (18, 2), (10, 34), (5, 438)]
    (codeMat 157) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane487GenSource0417 :
    QuotientRankAtLeast (spanCodes [273, 146, 82, 33, 10, 6]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(273, 442), (146, 438), (82, 406), (33, 133), (10, 170), (6, 45)]
    (codeMat 285) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane487GenSource0418 :
    QuotientRankAtLeast (spanCodes [273, 128, 83, 50, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(273, 318), (128, 45), (83, 287), (50, 137), (10, 139), (7, 1)]
    (codeMat 337) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane487GenSource0419 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 48, 10, 4]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 164), (144, 2), (80, 47), (48, 32), (10, 170), (4, 438)]
    (codeMat 342) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
