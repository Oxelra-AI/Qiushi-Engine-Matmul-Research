import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0100 :
    QuotientRankAtLeast (spanCodes [260, 134, 68, 37, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 432), (134, 462), (68, 180), (37, 420), (23, 475), (10, 191)]
    (codeMat 190) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0101 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 68), (128, 1), (68, 258), (32, 32), (20, 264), (10, 80)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane464GenSource0102 :
    QuotientRankAtLeast (spanCodes [277, 149, 68, 33, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(277, 465), (149, 97), (68, 420), (33, 283), (8, 192), (2, 260)]
    (codeMat 111) (codeMat 230) (codeMat 159) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0103 :
    QuotientRankAtLeast (spanCodes [263, 132, 68, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 433), (132, 223), (68, 367), (38, 283), (22, 475), (10, 420)]
    (codeMat 181) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane464GenSource0104 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 39, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (130, 130), (68, 150), (39, 104), (17, 97), (10, 105)]
    (codeMat 107) (codeMat 491) (codeMat 375) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0105 :
    QuotientRankAtLeast (spanCodes [278, 148, 68, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(278, 378), (148, 453), (68, 420), (32, 16), (10, 352), (1, 256)]
    (codeMat 87) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane464GenSource0106 :
    QuotientRankAtLeast (spanCodes [304, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 232), (178, 245), (66, 21), (10, 149), (6, 3), (1, 2)]
    (codeMat 417) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0107 :
    QuotientRankAtLeast (spanCodes [306, 176, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(306, 118), (176, 255), (64, 3), (10, 150), (4, 128), (1, 2)]
    (codeMat 141) (codeMat 403) (codeMat 403) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0108 :
    QuotientRankAtLeast (spanCodes [133, 68, 36, 21, 9, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(133, 408), (68, 136), (36, 1), (21, 46), (9, 2), (3, 32)]
    (codeMat 267) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane464GenSource0109 :
    QuotientRankAtLeast (spanCodes [133, 68, 36, 21, 8, 2]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(133, 133), (68, 170), (36, 438), (21, 134), (8, 32), (2, 2)]
    (codeMat 143) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
