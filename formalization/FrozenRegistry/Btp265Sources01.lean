import FrozenRegistry.Btp265Data
import QiushiCertifiedTransport
import QiushiMonoOrbit110From29
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit125From35
import QiushiMonoOrbit129From35T
import QiushiMonoOrbit130From35T
import QiushiWcOrbit113Dispatch
import QiushiWcOrbit127Dispatch
import QiushiWcOrbit128Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane265BtpGenSource0010 :
    QuotientRankAtLeast (spanCodes [272, 84, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(272, 349), (84, 92), (12, 13), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane265BtpGenSource0011 :
    QuotientRankAtLeast (spanCodes [272, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 12, 2, 1] [(272, 272), (96, 96), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit127_lb15_wc

theorem plane265BtpGenSource0012 :
    QuotientRankAtLeast (spanCodes [272, 100, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 12, 2, 1] [(272, 274), (100, 96), (12, 13), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit127_lb15_wc

theorem plane265BtpGenSource0013 :
    QuotientRankAtLeast (spanCodes [272, 112, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(272, 483), (112, 108), (12, 14), (2, 3), (1, 1)]
    (codeMat 473) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane265BtpGenSource0014 :
    QuotientRankAtLeast (spanCodes [272, 116, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(272, 480), (116, 111), (12, 15), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane265BtpGenSource0015 :
    QuotientRankAtLeast (spanCodes [272, 128, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(272, 104), (128, 8), (12, 133), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane265BtpGenSource0016 :
    QuotientRankAtLeast (spanCodes [272, 132, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(272, 96), (132, 12), (12, 132), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane265BtpGenSource0017 :
    QuotientRankAtLeast (spanCodes [272, 144, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 8, 2, 1] [(272, 387), (144, 3), (12, 105), (2, 1), (1, 8)]
    (codeMat 249) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit113_lb14_wc

theorem plane265BtpGenSource0018 :
    QuotientRankAtLeast (spanCodes [272, 148, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 132, 12, 2, 1] [(272, 422), (148, 132), (12, 14), (2, 2), (1, 1)]
    (codeMat 465) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit129_lb15_mono

theorem plane265BtpGenSource0019 :
    QuotientRankAtLeast (spanCodes [272, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 416), (160, 160), (12, 14), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

end QiushiMatmul
