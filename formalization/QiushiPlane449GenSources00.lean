import QiushiPlane449GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit311From196
import QiushiMonoOrbit320From196
import QiushiMonoOrbit340From196
import QiushiWcOrbit322Dispatch
import QiushiWcOrbit374Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane449GenSource0000 :
    QuotientRankAtLeast (spanCodes [310, 160, 10, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(310, 404), (160, 160), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane449GenSource0001 :
    QuotientRankAtLeast (spanCodes [306, 160, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 308), (160, 404), (14, 11), (1, 1)]
    (codeMat 473) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane449GenSource0002 :
    QuotientRankAtLeast (spanCodes [316, 160, 68, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(316, 404), (160, 170), (68, 10), (1, 1)]
    (codeMat 225) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane449GenSource0003 :
    QuotientRankAtLeast (spanCodes [316, 160, 70, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(316, 160), (160, 319), (70, 10), (1, 1)]
    (codeMat 169) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane449GenSource0004 :
    QuotientRankAtLeast (spanCodes [316, 160, 74, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(316, 170), (160, 319), (74, 10), (1, 1)]
    (codeMat 313) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane449GenSource0005 :
    QuotientRankAtLeast (spanCodes [316, 160, 76, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(316, 319), (160, 414), (76, 11), (1, 1)]
    (codeMat 369) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane449GenSource0006 :
    QuotientRankAtLeast (spanCodes [316, 160, 110, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [282, 160, 84, 1] [(316, 495), (160, 245), (110, 335), (1, 1)]
    (codeMat 249) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit374_lb17_wc

theorem plane449GenSource0007 :
    QuotientRankAtLeast (spanCodes [304, 160, 12, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(304, 160), (160, 400), (12, 10), (1, 1)]
    (codeMat 273) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane449GenSource0008 :
    QuotientRankAtLeast (spanCodes [300, 160, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(300, 96), (160, 11), (16, 1), (1, 384)]
    (codeMat 498) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane449GenSource0009 :
    QuotientRankAtLeast (spanCodes [302, 160, 18, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(302, 375), (160, 101), (18, 1), (1, 16)]
    (codeMat 331) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

end QiushiMatmul
