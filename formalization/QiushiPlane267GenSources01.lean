import QiushiPlane267GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit140Dispatch
import QiushiWcOrbit143Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane267GenSource0010 :
    QuotientRankAtLeast (spanCodes [412, 84, 32, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(412, 410), (84, 85), (32, 32), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane267GenSource0011 :
    QuotientRankAtLeast (spanCodes [72, 32, 28, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(72, 2), (32, 256), (28, 96), (2, 9), (1, 1)]
    (codeMat 177) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane267GenSource0012 :
    QuotientRankAtLeast (spanCodes [256, 84, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 84, 32, 2, 1] [(256, 32), (84, 84), (32, 256), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit140_lb14_wc

theorem plane267GenSource0013 :
    QuotientRankAtLeast (spanCodes [400, 84, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(400, 119), (84, 84), (32, 455), (2, 1), (1, 2)]
    (codeMat 233) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

theorem plane267GenSource0014 :
    QuotientRankAtLeast (spanCodes [404, 84, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(404, 118), (84, 86), (32, 455), (2, 1), (1, 2)]
    (codeMat 225) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

theorem plane267GenSource0015 :
    QuotientRankAtLeast (spanCodes [276, 144, 84, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 509), (144, 130), (84, 500), (32, 360), (12, 96), (2, 128), (1, 256)]
    (codeMat 95) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0016 :
    QuotientRankAtLeast (spanCodes [272, 148, 84, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 245), (148, 374), (84, 500), (32, 360), (12, 96), (2, 384), (1, 256)]
    (codeMat 93) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0017 :
    QuotientRankAtLeast (spanCodes [276, 148, 84, 32, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(276, 245), (148, 246), (84, 244), (32, 360), (12, 96), (2, 384), (1, 256)]
    (codeMat 92) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0018 :
    QuotientRankAtLeast (spanCodes [268, 136, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(268, 149), (136, 404), (64, 130), (32, 360), (20, 96), (2, 256), (1, 128)]
    (codeMat 93) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane267GenSource0019 :
    QuotientRankAtLeast (spanCodes [264, 132, 72, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 509), (132, 246), (72, 2), (32, 360), (28, 96), (2, 384), (1, 128)]
    (codeMat 94) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
