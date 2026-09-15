import QiushiPlane274GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiOrbit25FP
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit57Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane274GenSource0010 :
    QuotientRankAtLeast (spanCodes [260, 160, 80, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(260, 256), (160, 162), (80, 81), (12, 12), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane274GenSource0011 :
    QuotientRankAtLeast (spanCodes [256, 160, 80, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(256, 256), (160, 160), (80, 80), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane274GenSource0012 :
    QuotientRankAtLeast (spanCodes [260, 148, 80, 52, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 32), (148, 134), (80, 139), (52, 436), (2, 2), (1, 3)]
    (codeMat 489) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane274GenSource0013 :
    QuotientRankAtLeast (spanCodes [300, 160, 76, 28, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 96, 12, 2, 1] [(300, 109), (160, 408), (76, 13), (28, 133), (2, 3), (1, 1)]
    (codeMat 177) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit57_lb14_wc

theorem plane274GenSource0014 :
    QuotientRankAtLeast (spanCodes [308, 160, 80, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(308, 349), (160, 240), (80, 80), (12, 13), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane274GenSource0015 :
    QuotientRankAtLeast (spanCodes [280, 132, 80, 36, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 80, 12, 2, 1] [(280, 175), (132, 14), (80, 83), (36, 511), (2, 1), (1, 3)]
    (codeMat 489) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit56_lb14_unconditional

theorem plane274GenSource0016 :
    QuotientRankAtLeast (spanCodes [136, 80, 40, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(136, 88), (80, 80), (40, 256), (4, 6), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane274GenSource0017 :
    QuotientRankAtLeast (spanCodes [272, 160, 80, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(272, 88), (160, 80), (80, 344), (4, 2), (2, 3), (1, 6)]
    (codeMat 305) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane274GenSource0018 :
    QuotientRankAtLeast (spanCodes [288, 160, 80, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(288, 256), (160, 264), (80, 344), (4, 4), (2, 5), (1, 6)]
    (codeMat 417) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane274GenSource0019 :
    QuotientRankAtLeast (spanCodes [268, 128, 76, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(268, 245), (128, 2), (76, 246), (32, 360), (28, 96), (2, 128), (1, 384)]
    (codeMat 92) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
