import FrozenRegistry.Btp263Data
import QiushiCertifiedTransport
import QiushiMonoOrbit130From35T
import QiushiMonoOrbit131From55
import QiushiWcOrbit132Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane263BtpGenSource0020 :
    QuotientRankAtLeast (spanCodes [292, 160, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 12, 2, 1] [(292, 288), (160, 162), (12, 12), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit131_lb14_mono

theorem plane263BtpGenSource0021 :
    QuotientRankAtLeast (spanCodes [304, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(304, 304), (160, 160), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

theorem plane263BtpGenSource0022 :
    QuotientRankAtLeast (spanCodes [308, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(308, 304), (160, 162), (12, 12), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

theorem plane263BtpGenSource0023 :
    QuotientRankAtLeast (spanCodes [320, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(320, 256), (160, 173), (12, 12), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0024 :
    QuotientRankAtLeast (spanCodes [324, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(324, 257), (160, 175), (12, 12), (2, 2), (1, 1)]
    (codeMat 345) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0025 :
    QuotientRankAtLeast (spanCodes [336, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(336, 418), (160, 175), (12, 14), (2, 2), (1, 1)]
    (codeMat 473) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0026 :
    QuotientRankAtLeast (spanCodes [340, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(340, 419), (160, 173), (12, 14), (2, 2), (1, 1)]
    (codeMat 409) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0027 :
    QuotientRankAtLeast (spanCodes [352, 160, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 12, 2, 1] [(352, 301), (160, 173), (12, 12), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit131_lb14_mono

theorem plane263BtpGenSource0028 :
    QuotientRankAtLeast (spanCodes [356, 160, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 12, 2, 1] [(356, 300), (160, 175), (12, 12), (2, 2), (1, 1)]
    (codeMat 345) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit131_lb14_mono

theorem plane263BtpGenSource0029 :
    QuotientRankAtLeast (spanCodes [368, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(368, 319), (160, 173), (12, 12), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

end QiushiMatmul
