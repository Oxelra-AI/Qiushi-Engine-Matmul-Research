import FrozenRegistry.Btp227Data
import QiushiCertifiedTransport
import QiushiPlane269GenBindings01
import QiushiWcOrbit204Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane227BtpGenSource0010 :
    QuotientRankAtLeast (spanCodes [256, 140, 70, 38, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(256, 390), (140, 281), (70, 268), (38, 505), (16, 504), (1, 365)]
    (codeMat 491) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane227BtpGenSource0011 :
    QuotientRankAtLeast (spanCodes [270, 140, 72, 40, 16, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 8, 2, 1] [(270, 370), (140, 415), (72, 32), (40, 2), (16, 3), (1, 256)]
    (codeMat 114) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269GenBound0016

theorem plane227BtpGenSource0012 :
    QuotientRankAtLeast (spanCodes [268, 140, 74, 42, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 144, 68, 32, 10, 1] [(268, 381), (140, 380), (74, 306), (42, 280), (16, 32), (1, 144)]
    (codeMat 212) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc204s4Dispatch

theorem plane227BtpGenSource0013 :
    QuotientRankAtLeast (spanCodes [266, 140, 76, 44, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(266, 159), (140, 498), (76, 10), (44, 129), (16, 390), (1, 1)]
    (codeMat 249) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane227BtpGenSource0014 :
    QuotientRankAtLeast (spanCodes [264, 140, 78, 46, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(264, 371), (140, 396), (78, 97), (46, 148), (16, 504), (1, 365)]
    (codeMat 379) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

end QiushiMatmul
