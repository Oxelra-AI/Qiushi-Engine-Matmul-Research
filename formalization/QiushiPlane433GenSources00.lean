import QiushiPlane433GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit288From150
import QiushiMonoOrbit293From196
import QiushiMonoOrbit299From196
import QiushiMonoOrbit311From196
import QiushiMonoOrbit319From150
import QiushiPlane282GenFinal
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit264Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane433GenSource0000 :
    QuotientRankAtLeast (spanCodes [258, 16, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 264), (16, 1), (10, 10), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane433GenSource0001 :
    QuotientRankAtLeast (spanCodes [258, 16, 4, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(258, 12), (16, 256), (4, 1), (1, 2)]
    (codeMat 161) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane433GenSource0002 :
    QuotientRankAtLeast (spanCodes [258, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(258, 132), (16, 32), (12, 10), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane433GenSource0003 :
    QuotientRankAtLeast (spanCodes [258, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(258, 386), (16, 32), (14, 10), (1, 1)]
    (codeMat 337) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane433GenSource0004 :
    QuotientRankAtLeast (spanCodes [258, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(258, 392), (42, 10), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane433GenSource0005 :
    QuotientRankAtLeast (spanCodes [258, 36, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 100), (36, 1), (16, 32), (14, 21), (1, 63)]
    (codeMat 275) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane433GenSource0006 :
    QuotientRankAtLeast (spanCodes [258, 68, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(258, 20), (68, 10), (16, 256), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

theorem plane433GenSource0007 :
    QuotientRankAtLeast (spanCodes [258, 74, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [386, 32, 10, 1] [(258, 392), (74, 10), (16, 32), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit299_lb16_mono

theorem plane433GenSource0008 :
    QuotientRankAtLeast (spanCodes [258, 76, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(258, 96), (76, 10), (16, 384), (1, 1)]
    (codeMat 305) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane433GenSource0009 :
    QuotientRankAtLeast (spanCodes [258, 78, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(258, 388), (78, 11), (16, 292), (1, 1)]
    (codeMat 313) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

end QiushiMatmul
