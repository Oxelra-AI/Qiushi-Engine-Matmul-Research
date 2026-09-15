import QiushiPlane448GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit319From150
import QiushiMonoOrbit347From150
import QiushiMonoOrbit370From196
import QiushiWcOrbit218Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane448GenSource0020 :
    QuotientRankAtLeast (spanCodes [302, 160, 68, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(302, 142), (160, 238), (68, 10), (20, 435), (1, 1)]
    (codeMat 489) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane448GenSource0021 :
    QuotientRankAtLeast (spanCodes [300, 160, 66, 22, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(300, 440), (160, 466), (66, 11), (22, 133), (1, 1)]
    (codeMat 169) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane448GenSource0022 :
    QuotientRankAtLeast (spanCodes [300, 160, 78, 22, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(300, 96), (160, 238), (78, 10), (22, 435), (1, 1)]
    (codeMat 377) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane448GenSource0023 :
    QuotientRankAtLeast (spanCodes [302, 160, 74, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(302, 106), (160, 466), (74, 11), (20, 133), (1, 1)]
    (codeMat 185) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane448GenSource0024 :
    QuotientRankAtLeast (spanCodes [314, 160, 96, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(314, 171), (160, 389), (96, 388), (1, 292)]
    (codeMat 188) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane448GenSource0025 :
    QuotientRankAtLeast (spanCodes [314, 160, 100, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(314, 486), (160, 245), (100, 258), (1, 16)]
    (codeMat 207) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane448GenSource0026 :
    QuotientRankAtLeast (spanCodes [314, 160, 102, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 494), (160, 347), (102, 335), (1, 1)]
    (codeMat 169) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0027 :
    QuotientRankAtLeast (spanCodes [314, 160, 104, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 346), (160, 495), (104, 506), (1, 1)]
    (codeMat 481) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0028 :
    QuotientRankAtLeast (spanCodes [314, 160, 106, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 494), (160, 180), (106, 334), (1, 1)]
    (codeMat 177) (codeMat 405) (codeMat 407) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0029 :
    QuotientRankAtLeast (spanCodes [314, 160, 108, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(314, 181), (160, 347), (108, 20), (1, 1)]
    (codeMat 345) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

end QiushiMatmul
