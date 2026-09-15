import FrozenRegistry.Btp263Data
import QiushiCertifiedTransport
import FrozenRegistry.TransportBindings
import QiushiMonoOrbit118From31
import QiushiMonoOrbit123From35
import QiushiMonoOrbit97From31
import QiushiMonoOrbit99From35
import QiushiPlane426GenBindings07
import QiushiWcOrbit111Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane263BtpGenSource0000 :
    QuotientRankAtLeast (spanCodes [160, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 8, 4, 2, 1] [(160, 168), (8, 8), (4, 5), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.Transport.bound090

theorem plane263BtpGenSource0001 :
    QuotientRankAtLeast (spanCodes [160, 16, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 8, 2, 1] [(160, 104), (16, 8), (12, 29), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit97_lb15_mono

theorem plane263BtpGenSource0002 :
    QuotientRankAtLeast (spanCodes [160, 20, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 20, 8, 2, 1] [(160, 168), (20, 21), (12, 29), (2, 2), (1, 3)]
    (codeMat 273) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit99_lb15_mono

theorem plane263BtpGenSource0003 :
    QuotientRankAtLeast (spanCodes [128, 32, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(128, 3), (32, 256), (12, 96), (2, 1), (1, 8)]
    (codeMat 169) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane263BtpGenSource0004 :
    QuotientRankAtLeast (spanCodes [132, 36, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(132, 133), (36, 45), (12, 13), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane263BtpGenSource0005 :
    QuotientRankAtLeast (spanCodes [144, 48, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(144, 3), (48, 256), (12, 97), (2, 1), (1, 8)]
    (codeMat 185) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane263BtpGenSource0006 :
    QuotientRankAtLeast (spanCodes [148, 52, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 12, 2, 1] [(148, 135), (52, 47), (12, 15), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit118_lb15_mono

theorem plane263BtpGenSource0007 :
    QuotientRankAtLeast (spanCodes [160, 64, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 36, 8, 2, 1] [(160, 280), (64, 8), (12, 68), (2, 3), (1, 1)]
    (codeMat 161) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426GenBound0076

theorem plane263BtpGenSource0008 :
    QuotientRankAtLeast (spanCodes [160, 68, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 36, 8, 2, 1] [(160, 280), (68, 79), (12, 71), (2, 3), (1, 1)]
    (codeMat 177) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426GenBound0076

theorem plane263BtpGenSource0009 :
    QuotientRankAtLeast (spanCodes [160, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(160, 160), (80, 80), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

end QiushiMatmul
