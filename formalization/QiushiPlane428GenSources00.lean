import QiushiPlane428GenData
import QiushiCertifiedTransport
import QiushiStep126Mono253From96
import QiushiStep128Mono294From96
import QiushiWcOrbit156Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane428GenSource0000 :
    QuotientRankAtLeast (spanCodes [96, 16, 8, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 8, 2, 1] [(96, 68), (16, 2), (8, 1), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit253_lb16_mono

theorem plane428GenSource0001 :
    QuotientRankAtLeast (spanCodes [66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 32, 10, 1] [(66, 264), (34, 10), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit294_lb16_mono

theorem plane428GenSource0002 :
    QuotientRankAtLeast (spanCodes [74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 32, 10, 1] [(74, 264), (42, 10), (16, 1), (1, 32)]
    (codeMat 394) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit294_lb16_mono

theorem plane428GenSource0003 :
    QuotientRankAtLeast (spanCodes [68, 36, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 68), (36, 32), (16, 63), (14, 10), (1, 1)]
    (codeMat 281) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane428GenSource0004 :
    QuotientRankAtLeast (spanCodes [70, 38, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(70, 68), (38, 31), (16, 63), (12, 10), (1, 1)]
    (codeMat 281) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane428GenSource0005 :
    QuotientRankAtLeast (spanCodes [66, 34, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(66, 68), (34, 52), (16, 32), (14, 10), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane428GenSource0006 :
    QuotientRankAtLeast (spanCodes [66, 34, 16, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(66, 68), (34, 20), (16, 32), (12, 10), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane428GenSource0007 :
    QuotientRankAtLeast (spanCodes [138, 74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(138, 11), (74, 52), (42, 68), (16, 1), (1, 32)]
    (codeMat 122) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane428GenSource0008 :
    QuotientRankAtLeast (spanCodes [136, 74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(136, 11), (74, 20), (42, 68), (16, 1), (1, 32)]
    (codeMat 114) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane428GenSource0009 :
    QuotientRankAtLeast (spanCodes [138, 66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(138, 10), (66, 52), (34, 68), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

end QiushiMatmul
