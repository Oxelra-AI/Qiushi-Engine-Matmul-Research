import FrozenRegistry.Btp260Data
import QiushiCertifiedTransport
import FrozenRegistry.TransportBindings
import QiushiMonoOrbit123From35
import QiushiMonoOrbit124From35T
import QiushiMonoOrbit97From31
import QiushiOrbit101FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane260BtpGenSource0010 :
    QuotientRankAtLeast (spanCodes [132, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 8, 2, 1] [(132, 104), (80, 29), (12, 118), (2, 8), (1, 9)]
    (codeMat 377) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit97_lb15_mono

theorem plane260BtpGenSource0011 :
    QuotientRankAtLeast (spanCodes [144, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(144, 3), (80, 43), (12, 118), (2, 1), (1, 9)]
    (codeMat 377) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane260BtpGenSource0012 :
    QuotientRankAtLeast (spanCodes [148, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [148, 80, 12, 2, 1] [(148, 151), (80, 80), (12, 15), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.Transport.bound122

theorem plane260BtpGenSource0013 :
    QuotientRankAtLeast (spanCodes [160, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(160, 160), (80, 80), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

theorem plane260BtpGenSource0014 :
    QuotientRankAtLeast (spanCodes [164, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(164, 173), (80, 80), (12, 13), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

theorem plane260BtpGenSource0015 :
    QuotientRankAtLeast (spanCodes [176, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(176, 160), (80, 80), (12, 14), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

theorem plane260BtpGenSource0016 :
    QuotientRankAtLeast (spanCodes [180, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(180, 175), (80, 80), (12, 15), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

theorem plane260BtpGenSource0017 :
    QuotientRankAtLeast (spanCodes [256, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(256, 256), (80, 80), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane260BtpGenSource0018 :
    QuotientRankAtLeast (spanCodes [260, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(260, 256), (80, 81), (12, 12), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane260BtpGenSource0019 :
    QuotientRankAtLeast (spanCodes [272, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(272, 336), (80, 80), (12, 13), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

end QiushiMatmul
