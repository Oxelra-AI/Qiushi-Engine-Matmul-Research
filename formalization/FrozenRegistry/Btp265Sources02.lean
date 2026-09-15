import FrozenRegistry.Btp265Data
import QiushiCertifiedTransport
import QiushiMonoOrbit110From29
import QiushiMonoOrbit125From35
import QiushiMonoOrbit129From35T
import QiushiMonoOrbit130From35T
import QiushiWcOrbit113Dispatch
import QiushiWcOrbit132Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane265BtpGenSource0020 :
    QuotientRankAtLeast (spanCodes [272, 164, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 418), (164, 160), (12, 15), (2, 2), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane265BtpGenSource0021 :
    QuotientRankAtLeast (spanCodes [272, 176, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(272, 400), (176, 160), (12, 14), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

theorem plane265BtpGenSource0022 :
    QuotientRankAtLeast (spanCodes [272, 180, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(272, 402), (180, 162), (12, 15), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

theorem plane265BtpGenSource0023 :
    QuotientRankAtLeast (spanCodes [272, 192, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 8, 2, 1] [(272, 237), (192, 9), (12, 133), (2, 3), (1, 2)]
    (codeMat 169) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit110_lb15_mono

theorem plane265BtpGenSource0024 :
    QuotientRankAtLeast (spanCodes [272, 196, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(272, 232), (196, 13), (12, 133), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane265BtpGenSource0025 :
    QuotientRankAtLeast (spanCodes [272, 208, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 132, 12, 2, 1] [(272, 424), (208, 136), (12, 14), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit129_lb15_mono

theorem plane265BtpGenSource0026 :
    QuotientRankAtLeast (spanCodes [272, 212, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 8, 2, 1] [(272, 490), (212, 107), (12, 105), (2, 9), (1, 8)]
    (codeMat 241) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit113_lb14_wc

theorem plane265BtpGenSource0027 :
    QuotientRankAtLeast (spanCodes [272, 224, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 430), (224, 162), (12, 14), (2, 3), (1, 1)]
    (codeMat 465) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane265BtpGenSource0028 :
    QuotientRankAtLeast (spanCodes [272, 228, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 429), (228, 162), (12, 15), (2, 3), (1, 1)]
    (codeMat 409) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane265BtpGenSource0029 :
    QuotientRankAtLeast (spanCodes [272, 240, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(272, 413), (240, 175), (12, 15), (2, 3), (1, 1)]
    (codeMat 345) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

end QiushiMatmul
