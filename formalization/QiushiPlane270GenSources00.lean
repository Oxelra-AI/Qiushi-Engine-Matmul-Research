import QiushiPlane270GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit121From55
import QiushiMonoOrbit126From55
import QiushiMonoOrbit137From55
import QiushiMonoOrbit142From56
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit119Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane270GenSource0000 :
    QuotientRankAtLeast (spanCodes [320, 32, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(320, 256), (32, 45), (12, 12), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane270GenSource0001 :
    QuotientRankAtLeast (spanCodes [320, 32, 20, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(320, 384), (32, 32), (20, 12), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane270GenSource0002 :
    QuotientRankAtLeast (spanCodes [320, 32, 28, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(320, 384), (32, 32), (28, 12), (2, 3), (1, 2)]
    (codeMat 273) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane270GenSource0003 :
    QuotientRankAtLeast (spanCodes [260, 68, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(260, 32), (68, 13), (32, 256), (2, 2), (1, 1)]
    (codeMat 169) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane270GenSource0004 :
    QuotientRankAtLeast (spanCodes [264, 72, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(264, 352), (72, 8), (32, 256), (2, 2), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane270GenSource0005 :
    QuotientRankAtLeast (spanCodes [268, 76, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 12, 2, 1] [(268, 352), (76, 13), (32, 256), (2, 2), (1, 1)]
    (codeMat 185) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit126_lb14_mono

theorem plane270GenSource0006 :
    QuotientRankAtLeast (spanCodes [272, 80, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 80, 32, 2, 1] [(272, 272), (80, 80), (32, 32), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit137_lb14_mono

theorem plane270GenSource0007 :
    QuotientRankAtLeast (spanCodes [276, 84, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 2, 1] [(276, 272), (84, 85), (32, 32), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit142_lb14_mono

theorem plane270GenSource0008 :
    QuotientRankAtLeast (spanCodes [280, 88, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 80, 32, 2, 1] [(280, 272), (88, 80), (32, 32), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit137_lb14_mono

theorem plane270GenSource0009 :
    QuotientRankAtLeast (spanCodes [284, 92, 32, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 2, 1] [(284, 272), (92, 85), (32, 32), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit142_lb14_mono

end QiushiMatmul
