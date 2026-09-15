import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0100 :
    QuotientRankAtLeast (spanCodes [256, 162, 68, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 320), (162, 238), (68, 69), (20, 437), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane453GenSource0101 :
    QuotientRankAtLeast (spanCodes [260, 166, 68, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 27), (166, 228), (68, 11), (20, 507), (10, 79), (1, 1)]
    (codeMat 417) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane453GenSource0102 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 3), (68, 150), (36, 128), (20, 136), (10, 232)]
    (codeMat 212) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane453GenSource0103 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (130, 128), (68, 150), (39, 252), (20, 224), (10, 255)]
    (codeMat 110) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane453GenSource0104 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 22), (68, 148), (32, 3), (20, 31), (10, 252)]
    (codeMat 102) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane453GenSource0105 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (135, 149), (68, 150), (34, 104), (20, 96), (10, 232)]
    (codeMat 157) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane453GenSource0106 :
    QuotientRankAtLeast (spanCodes [256, 160, 65, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 1), (160, 78), (65, 260), (17, 176), (10, 160), (5, 320)]
    (codeMat 92) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane453GenSource0107 :
    QuotientRankAtLeast (spanCodes [417, 64, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(417, 340), (64, 128), (16, 1), (10, 10), (4, 32)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane453GenSource0108 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 69), (160, 170), (64, 260), (16, 16), (10, 160), (4, 320)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane453GenSource0109 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 260), (160, 160), (68, 68), (20, 436), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
