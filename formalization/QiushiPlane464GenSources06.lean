import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0060 :
    QuotientRankAtLeast (spanCodes [133, 68, 32, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(133, 252), (68, 224), (32, 128), (17, 10), (9, 8), (3, 3)]
    (codeMat 275) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0061 :
    QuotientRankAtLeast (spanCodes [133, 68, 33, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(133, 96), (68, 232), (33, 30), (16, 1), (8, 3), (2, 8)]
    (codeMat 330) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0062 :
    QuotientRankAtLeast (spanCodes [133, 68, 37, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(133, 316), (68, 113), (37, 62), (20, 52), (8, 1), (2, 32)]
    (codeMat 394) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane464GenSource0063 :
    QuotientRankAtLeast (spanCodes [128, 66, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(128, 1), (66, 10), (50, 268), (10, 138), (6, 32)]
    (codeMat 396) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane464GenSource0064 :
    QuotientRankAtLeast (spanCodes [129, 66, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(129, 11), (66, 10), (51, 300), (10, 138), (6, 32)]
    (codeMat 397) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane464GenSource0065 :
    QuotientRankAtLeast (spanCodes [128, 68, 32, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(128, 365), (68, 113), (32, 63), (20, 21), (9, 1), (3, 32)]
    (codeMat 395) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane464GenSource0066 :
    QuotientRankAtLeast (spanCodes [128, 68, 37, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(128, 128), (68, 224), (37, 28), (17, 10), (9, 3), (3, 8)]
    (codeMat 267) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0067 :
    QuotientRankAtLeast (spanCodes [129, 68, 37, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 31), (68, 252), (37, 139), (16, 1), (8, 9), (2, 3)]
    (codeMat 282) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane464GenSource0068 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (160, 160), (68, 68), (20, 436), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane464GenSource0069 :
    QuotientRankAtLeast (spanCodes [260, 162, 68, 22, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 27), (162, 238), (68, 11), (22, 437), (10, 78), (1, 1)]
    (codeMat 417) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
