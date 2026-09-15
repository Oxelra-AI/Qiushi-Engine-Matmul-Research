import FrozenRegistry.Btp263Data
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit123From35
import QiushiMonoOrbit125From35
import QiushiMonoOrbit130From35T
import QiushiMonoOrbit131From55
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane263BtpGenSource0010 :
    QuotientRankAtLeast (spanCodes [160, 84, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 12, 2, 1] [(160, 240), (84, 94), (12, 14), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit123_lb15_mono

theorem plane263BtpGenSource0011 :
    QuotientRankAtLeast (spanCodes [160, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(160, 283), (96, 280), (12, 96), (2, 9), (1, 8)]
    (codeMat 169) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane263BtpGenSource0012 :
    QuotientRankAtLeast (spanCodes [160, 100, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(160, 232), (100, 109), (12, 13), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane263BtpGenSource0013 :
    QuotientRankAtLeast (spanCodes [160, 112, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 96, 12, 2, 1] [(160, 232), (112, 96), (12, 14), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit125_lb15_mono

theorem plane263BtpGenSource0014 :
    QuotientRankAtLeast (spanCodes [160, 116, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(160, 371), (116, 281), (12, 105), (2, 9), (1, 8)]
    (codeMat 249) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane263BtpGenSource0015 :
    QuotientRankAtLeast (spanCodes [256, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(256, 256), (160, 160), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0016 :
    QuotientRankAtLeast (spanCodes [260, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(260, 256), (160, 162), (12, 12), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0017 :
    QuotientRankAtLeast (spanCodes [272, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(272, 416), (160, 160), (12, 14), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0018 :
    QuotientRankAtLeast (spanCodes [276, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 12, 2, 1] [(276, 416), (160, 162), (12, 14), (2, 2), (1, 1)]
    (codeMat 465) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit130_lb15_mono

theorem plane263BtpGenSource0019 :
    QuotientRankAtLeast (spanCodes [288, 160, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 12, 2, 1] [(288, 288), (160, 160), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit131_lb14_mono

end QiushiMatmul
