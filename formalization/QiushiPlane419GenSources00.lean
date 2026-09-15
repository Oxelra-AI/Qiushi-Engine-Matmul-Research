import QiushiPlane419GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit293From196
import QiushiStep126Mono251From96
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit264Dispatch
import QiushiWcOrbit290Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane419GenSource0000 :
    QuotientRankAtLeast (spanCodes [68, 32, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(68, 68), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane419GenSource0001 :
    QuotientRankAtLeast (spanCodes [70, 32, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 10, 1] [(70, 78), (32, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit290_lb17_wc

theorem plane419GenSource0002 :
    QuotientRankAtLeast (spanCodes [32, 10, 4, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [20, 8, 2, 1] [(32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit251_lb16_mono

theorem plane419GenSource0003 :
    QuotientRankAtLeast (spanCodes [64, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(64, 2), (32, 256), (10, 12), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane419GenSource0004 :
    QuotientRankAtLeast (spanCodes [66, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(66, 14), (32, 256), (10, 12), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane419GenSource0005 :
    QuotientRankAtLeast (spanCodes [68, 32, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 68), (32, 32), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0006 :
    QuotientRankAtLeast (spanCodes [70, 32, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(70, 68), (32, 63), (22, 31), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0007 :
    QuotientRankAtLeast (spanCodes [68, 32, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 68), (32, 32), (22, 31), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane419GenSource0008 :
    QuotientRankAtLeast (spanCodes [132, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(132, 132), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

theorem plane419GenSource0009 :
    QuotientRankAtLeast (spanCodes [134, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 10, 1] [(134, 132), (32, 32), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit293_lb16_mono

end QiushiMatmul
