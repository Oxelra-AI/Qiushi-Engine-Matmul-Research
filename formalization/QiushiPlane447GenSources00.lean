import QiushiPlane447GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit288From150
import QiushiStep128Mono343From214
import QiushiWcOrbit322Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane447GenSource0000 :
    QuotientRankAtLeast (spanCodes [306, 160, 12, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 160), (160, 404), (12, 11), (1, 1)]
    (codeMat 345) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane447GenSource0001 :
    QuotientRankAtLeast (spanCodes [306, 160, 14, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 308), (160, 404), (14, 11), (1, 1)]
    (codeMat 473) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane447GenSource0002 :
    QuotientRankAtLeast (spanCodes [306, 160, 66, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 404), (160, 308), (66, 10), (1, 1)]
    (codeMat 481) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane447GenSource0003 :
    QuotientRankAtLeast (spanCodes [306, 160, 68, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 404), (160, 160), (68, 10), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane447GenSource0004 :
    QuotientRankAtLeast (spanCodes [306, 160, 74, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 160), (160, 308), (74, 10), (1, 1)]
    (codeMat 369) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane447GenSource0005 :
    QuotientRankAtLeast (spanCodes [306, 160, 78, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(306, 308), (160, 160), (78, 10), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane447GenSource0006 :
    QuotientRankAtLeast (spanCodes [290, 160, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(290, 31), (160, 11), (16, 1), (1, 256)]
    (codeMat 98) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

theorem plane447GenSource0007 :
    QuotientRankAtLeast (spanCodes [294, 160, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(294, 31), (160, 30), (20, 20), (1, 256)]
    (codeMat 93) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

theorem plane447GenSource0008 :
    QuotientRankAtLeast (spanCodes [292, 160, 22, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 20, 10, 1] [(292, 1), (160, 30), (22, 20), (1, 256)]
    (codeMat 95) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit288_lb16_mono

theorem plane447GenSource0009 :
    QuotientRankAtLeast (spanCodes [298, 160, 24, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [298, 100, 16, 1] [(298, 351), (160, 101), (24, 1), (1, 16)]
    (codeMat 266) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit343_lb16_mono

end QiushiMatmul
