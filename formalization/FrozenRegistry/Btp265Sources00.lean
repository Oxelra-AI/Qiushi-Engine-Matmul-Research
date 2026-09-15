import FrozenRegistry.Btp265Data
import QiushiCertifiedTransport
import FrozenRegistry.TransportBindings
import QiushiMonoOrbit100From34
import QiushiMonoOrbit121From55
import QiushiMonoOrbit124From35T
import QiushiOrbit29FP
import QiushiPlane426GenBindings07
import QiushiStep99Orbit120Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane265BtpGenSource0000 :
    QuotientRankAtLeast (spanCodes [272, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 8, 4, 2, 1] [(272, 168), (8, 8), (4, 2), (2, 5), (1, 1)]
    (codeMat 273) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.Transport.bound090

theorem plane265BtpGenSource0001 :
    QuotientRankAtLeast (spanCodes [256, 16, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 8, 2, 1] [(256, 256), (16, 8), (12, 28), (2, 1), (1, 3)]
    (codeMat 273) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit100_lb14_mono

theorem plane265BtpGenSource0002 :
    QuotientRankAtLeast (spanCodes [260, 20, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 8, 2, 1] [(260, 256), (20, 20), (12, 28), (2, 2), (1, 3)]
    (codeMat 337) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit100_lb14_mono

theorem plane265BtpGenSource0003 :
    QuotientRankAtLeast (spanCodes [272, 32, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(272, 272), (32, 32), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane265BtpGenSource0004 :
    QuotientRankAtLeast (spanCodes [272, 36, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 12, 2, 1] [(272, 274), (36, 32), (12, 13), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit120_lb15_unconditional

theorem plane265BtpGenSource0005 :
    QuotientRankAtLeast (spanCodes [272, 48, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(272, 416), (48, 32), (12, 14), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane265BtpGenSource0006 :
    QuotientRankAtLeast (spanCodes [272, 52, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 12, 2, 1] [(272, 418), (52, 34), (12, 15), (2, 2), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit121_lb14_mono

theorem plane265BtpGenSource0007 :
    QuotientRankAtLeast (spanCodes [272, 64, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(272, 168), (64, 8), (12, 69), (2, 2), (1, 1)]
    (codeMat 161) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane265BtpGenSource0008 :
    QuotientRankAtLeast (spanCodes [272, 68, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 68, 36, 8, 2, 1] [(272, 280), (68, 71), (12, 79), (2, 3), (1, 1)]
    (codeMat 305) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane426GenBound0076

theorem plane265BtpGenSource0009 :
    QuotientRankAtLeast (spanCodes [272, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(272, 336), (80, 80), (12, 13), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

end QiushiMatmul
