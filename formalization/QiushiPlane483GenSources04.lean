import QiushiPlane483GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit440From373
import QiushiMonoOrbit443From373
import QiushiMonoOrbit444From373
import QiushiMonoOrbit446From373
import QiushiWcOrbit322Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane483GenSource0040 :
    QuotientRankAtLeast (spanCodes [282, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(282, 244), (160, 160), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0041 :
    QuotientRankAtLeast (spanCodes [284, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 84, 1] [(284, 160), (160, 245), (1, 1)]
    (codeMat 377) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit444_lb17_mono

theorem plane483GenSource0042 :
    QuotientRankAtLeast (spanCodes [286, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [224, 20, 1] [(286, 244), (160, 224), (1, 1)]
    (codeMat 185) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit440_lb17_mono

theorem plane483GenSource0043 :
    QuotientRankAtLeast (spanCodes [300, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(300, 21), (160, 287), (1, 1)]
    (codeMat 313) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0044 :
    QuotientRankAtLeast (spanCodes [302, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 20, 1] [(302, 266), (160, 287), (1, 1)]
    (codeMat 425) (codeMat 405) (codeMat 407) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit443_lb17_mono

theorem plane483GenSource0045 :
    QuotientRankAtLeast (spanCodes [304, 160, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 1] [(304, 400), (160, 160), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit446_lb17_mono

theorem plane483GenSource0046 :
    QuotientRankAtLeast (spanCodes [308, 160, 12, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(308, 160), (160, 308), (12, 10), (1, 1)]
    (codeMat 465) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane483GenSource0047 :
    QuotientRankAtLeast (spanCodes [310, 160, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(310, 404), (160, 308), (14, 10), (1, 1)]
    (codeMat 337) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane483GenSource0048 :
    QuotientRankAtLeast (spanCodes [306, 160, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 308), (160, 404), (14, 11), (1, 1)]
    (codeMat 473) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane483GenSource0049 :
    QuotientRankAtLeast (spanCodes [306, 160, 12, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 160), (160, 404), (12, 11), (1, 1)]
    (codeMat 345) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

end QiushiMatmul
