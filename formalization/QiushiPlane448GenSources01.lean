import QiushiPlane448GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit319From150
import QiushiMonoOrbit320From196
import QiushiMonoOrbit347From150
import QiushiMonoOrbit370From196
import QiushiStep99Orbit150Dispatch
import QiushiWcOrbit202Dispatch
import QiushiWcOrbit204Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane448GenSource0010 :
    QuotientRankAtLeast (spanCodes [268, 150, 54, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(268, 160), (150, 398), (54, 1), (1, 292)]
    (codeMat 379) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane448GenSource0011 :
    QuotientRankAtLeast (spanCodes [258, 152, 56, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 228, 16, 1] [(258, 259), (152, 503), (56, 16), (1, 1)]
    (codeMat 337) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit347_lb16_mono

theorem plane448GenSource0012 :
    QuotientRankAtLeast (spanCodes [258, 150, 54, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 264), (150, 333), (54, 1), (14, 26), (1, 16)]
    (codeMat 331) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane448GenSource0013 :
    QuotientRankAtLeast (spanCodes [256, 154, 58, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [292, 160, 10, 1] [(256, 1), (154, 160), (58, 170), (1, 292)]
    (codeMat 468) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit319_lb16_mono

theorem plane448GenSource0014 :
    QuotientRankAtLeast (spanCodes [262, 156, 60, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(262, 20), (156, 334), (60, 506), (1, 1)]
    (codeMat 489) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane448GenSource0015 :
    QuotientRankAtLeast (spanCodes [314, 160, 70, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(314, 161), (160, 315), (70, 10), (1, 1)]
    (codeMat 233) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane448GenSource0016 :
    QuotientRankAtLeast (spanCodes [308, 160, 68, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(308, 274), (160, 176), (68, 10), (14, 68), (1, 1)]
    (codeMat 161) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane448GenSource0017 :
    QuotientRankAtLeast (spanCodes [314, 160, 76, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(314, 410), (160, 315), (76, 10), (1, 1)]
    (codeMat 249) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane448GenSource0018 :
    QuotientRankAtLeast (spanCodes [308, 160, 66, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 68, 10, 1] [(308, 315), (160, 479), (66, 11), (14, 69), (1, 1)]
    (codeMat 225) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit202_lb16_wc

theorem plane448GenSource0019 :
    QuotientRankAtLeast (spanCodes [310, 160, 66, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(310, 487), (160, 280), (66, 11), (12, 68), (1, 1)]
    (codeMat 161) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

end QiushiMatmul
