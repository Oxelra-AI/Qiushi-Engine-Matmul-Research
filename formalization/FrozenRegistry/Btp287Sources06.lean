import FrozenRegistry.Btp287Data
import QiushiCertifiedTransport
import FrozenRegistry.TransportBindings
import QiushiMonoOrbit174From65
import QiushiOrbit14FP
import QiushiPlane315GenBindings00
import QiushiPlane315GenBindings01
import QiushiStep126Mono175From75
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane287BtpGenSource0060 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (160, 224), (96, 96), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane287BtpGenSource0061 :
    QuotientRankAtLeast (spanCodes [354, 160, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 160, 20, 10, 1] [(354, 445), (160, 191), (20, 21), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.FrozenRegistry.Transport.bound173

theorem plane287BtpGenSource0062 :
    QuotientRankAtLeast (spanCodes [356, 160, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(356, 440), (160, 191), (20, 21), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane287BtpGenSource0063 :
    QuotientRankAtLeast (spanCodes [262, 160, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 453), (160, 21), (96, 20), (20, 170), (10, 357), (1, 260)]
    (codeMat 340) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0017

theorem plane287BtpGenSource0064 :
    QuotientRankAtLeast (spanCodes [288, 160, 70, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 16), (160, 336), (70, 69), (20, 506), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315GenBound0009

theorem plane287BtpGenSource0065 :
    QuotientRankAtLeast (spanCodes [262, 130, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 224), (130, 256), (66, 104), (34, 227), (20, 284), (10, 97), (1, 8)]
    (codeMat 335) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane287BtpGenSource0066 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 387), (128, 384), (64, 128), (32, 360), (20, 245), (10, 278), (1, 130)]
    (codeMat 309) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane287BtpGenSource0067 :
    QuotientRankAtLeast (spanCodes [358, 160, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 20, 10, 1] [(358, 442), (160, 191), (20, 21), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit174_lb15_mono

end QiushiMatmul
