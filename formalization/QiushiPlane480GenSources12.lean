import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit252From101
import QiushiStep126Mono250From93
import QiushiWcOrbit281Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0120 :
    QuotientRankAtLeast (spanCodes [390, 70, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(390, 27), (70, 26), (16, 256), (1, 16)]
    (codeMat 140) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0121 :
    QuotientRankAtLeast (spanCodes [364, 170, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(364, 283), (170, 26), (16, 16), (1, 256)]
    (codeMat 85) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0122 :
    QuotientRankAtLeast (spanCodes [384, 70, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(384, 1), (70, 10), (16, 256), (1, 16)]
    (codeMat 140) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0123 :
    QuotientRankAtLeast (spanCodes [320, 168, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(320, 1), (168, 10), (16, 16), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0124 :
    QuotientRankAtLeast (spanCodes [422, 78, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(422, 283), (78, 26), (16, 256), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0125 :
    QuotientRankAtLeast (spanCodes [324, 170, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(324, 257), (170, 10), (16, 16), (1, 256)]
    (codeMat 85) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0126 :
    QuotientRankAtLeast (spanCodes [416, 78, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(416, 257), (78, 10), (16, 256), (1, 16)]
    (codeMat 142) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0127 :
    QuotientRankAtLeast (spanCodes [16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [16, 8, 2, 1] [(16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit250_lb15_mono

theorem plane480GenSource0128 :
    QuotientRankAtLeast (spanCodes [16, 8, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(16, 2), (8, 1), (4, 32), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0129 :
    QuotientRankAtLeast (spanCodes [16, 8, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(16, 2), (8, 1), (6, 32), (1, 8)]
    (codeMat 266) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

end QiushiMatmul
