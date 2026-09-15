import QiushiPlane270GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit121From55
import QiushiMonoOrbit131From55
import QiushiMonoOrbit137From55
import QiushiMonoOrbit142From56
import QiushiWcOrbit143Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane270GenSource0010 :
    QuotientRankAtLeast (spanCodes [320, 132, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(320, 32), (132, 14), (32, 384), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane270GenSource0011 :
    QuotientRankAtLeast (spanCodes [320, 136, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 80, 32, 2, 1] [(320, 32), (136, 80), (32, 320), (2, 2), (1, 1)]
    (codeMat 161) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit137_lb14_mono

theorem plane270GenSource0012 :
    QuotientRankAtLeast (spanCodes [320, 140, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 2, 1] [(320, 32), (140, 84), (32, 325), (2, 2), (1, 1)]
    (codeMat 225) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit142_lb14_mono

theorem plane270GenSource0013 :
    QuotientRankAtLeast (spanCodes [320, 148, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 12, 2, 1] [(320, 288), (148, 14), (32, 384), (2, 1), (1, 2)]
    (codeMat 177) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit131_lb14_mono

theorem plane270GenSource0014 :
    QuotientRankAtLeast (spanCodes [320, 156, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(320, 32), (156, 86), (32, 455), (2, 2), (1, 3)]
    (codeMat 225) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

theorem plane270GenSource0015 :
    QuotientRankAtLeast (spanCodes [320, 196, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(320, 32), (196, 14), (32, 384), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane270GenSource0016 :
    QuotientRankAtLeast (spanCodes [320, 200, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 80, 32, 2, 1] [(320, 32), (200, 80), (32, 320), (2, 3), (1, 1)]
    (codeMat 161) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit137_lb14_mono

theorem plane270GenSource0017 :
    QuotientRankAtLeast (spanCodes [320, 204, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 2, 1] [(320, 32), (204, 84), (32, 325), (2, 3), (1, 1)]
    (codeMat 225) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit142_lb14_mono

theorem plane270GenSource0018 :
    QuotientRankAtLeast (spanCodes [320, 212, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(320, 32), (212, 86), (32, 455), (2, 1), (1, 3)]
    (codeMat 225) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

theorem plane270GenSource0019 :
    QuotientRankAtLeast (spanCodes [320, 220, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 12, 2, 1] [(320, 288), (220, 14), (32, 384), (2, 3), (1, 2)]
    (codeMat 177) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit131_lb14_mono

end QiushiMatmul
