import QiushiPlane433GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit288From150
import QiushiMonoOrbit293From196
import QiushiMonoOrbit299From196
import QiushiMonoOrbit311From196
import QiushiMonoOrbit340From196
import QiushiMonoOrbit342From196
import QiushiStep128Mono344From201T
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit264Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane433GenSource0010 :
    QuotientRankAtLeast (spanCodes [258, 74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 392), (74, 268), (42, 10), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane433GenSource0011 :
    QuotientRankAtLeast (spanCodes [258, 100, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(258, 258), (100, 100), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane433GenSource0012 :
    QuotientRankAtLeast (spanCodes [258, 102, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 100, 16, 1] [(258, 386), (102, 116), (16, 16), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit344_lb16_mono

theorem plane433GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 128, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(258, 12), (128, 1), (16, 2), (1, 256)]
    (codeMat 84) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane433GenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 136, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(258, 132), (136, 10), (16, 1), (1, 32)]
    (codeMat 98) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane433GenSource0015 :
    QuotientRankAtLeast (spanCodes [258, 134, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 386), (134, 262), (16, 32), (14, 10), (1, 1)]
    (codeMat 337) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane433GenSource0016 :
    QuotientRankAtLeast (spanCodes [258, 138, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(258, 386), (138, 10), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane433GenSource0017 :
    QuotientRankAtLeast (spanCodes [258, 160, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(258, 20), (160, 10), (16, 1), (1, 256)]
    (codeMat 98) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

theorem plane433GenSource0018 :
    QuotientRankAtLeast (spanCodes [258, 166, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [296, 100, 16, 1] [(258, 296), (166, 100), (16, 1), (1, 16)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit342_lb16_mono

theorem plane433GenSource0019 :
    QuotientRankAtLeast (spanCodes [258, 168, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(258, 96), (168, 10), (16, 1), (1, 384)]
    (codeMat 98) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

end QiushiMatmul
