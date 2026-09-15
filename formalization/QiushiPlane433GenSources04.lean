import QiushiPlane433GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit111Dispatch
import QiushiWcOrbit143Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane433GenSource0040 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 68), (128, 1), (64, 8), (16, 2), (10, 20), (1, 32)]
    (codeMat 84) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane433GenSource0041 :
    QuotientRankAtLeast (spanCodes [258, 128, 72, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 118), (128, 9), (72, 2), (42, 96), (16, 8), (1, 128)]
    (codeMat 86) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane433GenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 136, 76, 34, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 420), (136, 186), (76, 69), (34, 160), (16, 16), (1, 320)]
    (codeMat 87) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane433GenSource0043 :
    QuotientRankAtLeast (spanCodes [258, 194, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 263), (194, 262), (42, 300), (16, 32), (1, 390)]
    (codeMat 340) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane433GenSource0044 :
    QuotientRankAtLeast (spanCodes [256, 68, 16, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(256, 256), (68, 96), (16, 2), (2, 1), (1, 8)]
    (codeMat 273) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane433GenSource0045 :
    QuotientRankAtLeast (spanCodes [256, 160, 16, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(256, 256), (160, 96), (16, 8), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane433GenSource0046 :
    QuotientRankAtLeast (spanCodes [258, 162, 16, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(258, 361), (162, 96), (16, 256), (6, 1), (1, 2)]
    (codeMat 185) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane433GenSource0047 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(258, 361), (130, 1), (70, 96), (16, 2), (1, 256)]
    (codeMat 85) (codeMat 358) (codeMat 158) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane433GenSource0048 :
    QuotientRankAtLeast (spanCodes [258, 130, 106, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 2, 1] [(258, 434), (130, 2), (106, 117), (16, 1), (1, 32)]
    (codeMat 106) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit143_lb14_wc

theorem plane433GenSource0049 :
    QuotientRankAtLeast (spanCodes [258, 130, 78, 34, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(258, 46), (130, 3), (78, 274), (34, 14), (16, 1), (1, 438)]
    (codeMat 442) (codeMat 107) (codeMat 428) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

end QiushiMatmul
