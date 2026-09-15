import FrozenRegistry.Btp261Data
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit125From35
import QiushiMonoOrbit126From55
import QiushiOrbit23FP
import QiushiWcOrbit127Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane261BtpGenSource0010 :
    QuotientRankAtLeast (spanCodes [144, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(144, 3), (96, 368), (12, 104), (2, 1), (1, 8)]
    (codeMat 249) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane261BtpGenSource0011 :
    QuotientRankAtLeast (spanCodes [148, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(148, 133), (96, 96), (12, 13), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane261BtpGenSource0012 :
    QuotientRankAtLeast (spanCodes [160, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(160, 283), (96, 280), (12, 96), (2, 9), (1, 8)]
    (codeMat 169) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane261BtpGenSource0013 :
    QuotientRankAtLeast (spanCodes [164, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(164, 228), (96, 96), (12, 12), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane261BtpGenSource0014 :
    QuotientRankAtLeast (spanCodes [176, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(176, 232), (96, 96), (12, 13), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane261BtpGenSource0015 :
    QuotientRankAtLeast (spanCodes [180, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(180, 283), (96, 368), (12, 104), (2, 9), (1, 8)]
    (codeMat 249) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane261BtpGenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 96, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 12, 2, 1] [(256, 256), (96, 96), (12, 12), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit126_lb14_mono

theorem plane261BtpGenSource0017 :
    QuotientRankAtLeast (spanCodes [256, 96, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 128), (96, 80), (8, 8), (4, 2), (2, 7), (1, 1)]
    (codeMat 273) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane261BtpGenSource0018 :
    QuotientRankAtLeast (spanCodes [260, 96, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 12, 2, 1] [(260, 256), (96, 97), (12, 12), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit126_lb14_mono

theorem plane261BtpGenSource0019 :
    QuotientRankAtLeast (spanCodes [272, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 12, 2, 1] [(272, 272), (96, 96), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit127_lb15_wc

end QiushiMatmul
