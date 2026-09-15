import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0070 :
    QuotientRankAtLeast (spanCodes [133, 68, 33, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(133, 96), (68, 232), (33, 30), (16, 1), (8, 3), (2, 8)]
    (codeMat 330) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane468GenSource0071 :
    QuotientRankAtLeast (spanCodes [134, 67, 34, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(134, 350), (67, 469), (34, 43), (23, 33), (10, 42)]
    (codeMat 410) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane468GenSource0072 :
    QuotientRankAtLeast (spanCodes [132, 66, 32, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(132, 278), (66, 139), (32, 32), (22, 406), (10, 138)]
    (codeMat 470) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane468GenSource0073 :
    QuotientRankAtLeast (spanCodes [129, 69, 37, 17, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 136), (69, 224), (37, 28), (17, 10), (9, 3), (3, 8)]
    (codeMat 331) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane468GenSource0074 :
    QuotientRankAtLeast (spanCodes [129, 68, 37, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 31), (68, 252), (37, 139), (16, 1), (8, 9), (2, 3)]
    (codeMat 282) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane468GenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 164, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (164, 79), (70, 160), (18, 1), (10, 26), (1, 16)]
    (codeMat 331) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0076 :
    QuotientRankAtLeast (spanCodes [258, 164, 66, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(258, 440), (164, 463), (66, 408), (22, 118), (10, 411)]
    (codeMat 102) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane468GenSource0077 :
    QuotientRankAtLeast (spanCodes [273, 161, 81, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(273, 410), (161, 442), (81, 411), (10, 493), (5, 2)]
    (codeMat 396) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane468GenSource0078 :
    QuotientRankAtLeast (spanCodes [257, 161, 64, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 11), (161, 213), (64, 1), (17, 352), (10, 96), (5, 16)]
    (codeMat 204) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane468GenSource0079 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 69), (160, 170), (64, 260), (16, 16), (10, 160), (4, 320)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
