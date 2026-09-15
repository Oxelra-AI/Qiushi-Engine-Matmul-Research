import QiushiPlane413GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit252From101
import QiushiMonoOrbit259From120
import QiushiWcOrbit264Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane413GenSource0000 :
    QuotientRankAtLeast (spanCodes [68, 32, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(68, 12), (32, 256), (2, 2), (1, 1)]
    (codeMat 161) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane413GenSource0001 :
    QuotientRankAtLeast (spanCodes [76, 32, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(76, 12), (32, 256), (2, 2), (1, 1)]
    (codeMat 177) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane413GenSource0002 :
    QuotientRankAtLeast (spanCodes [132, 32, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(132, 12), (32, 256), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane413GenSource0003 :
    QuotientRankAtLeast (spanCodes [148, 32, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(148, 12), (32, 256), (2, 1), (1, 2)]
    (codeMat 177) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane413GenSource0004 :
    QuotientRankAtLeast (spanCodes [196, 32, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(196, 12), (32, 256), (2, 2), (1, 3)]
    (codeMat 161) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane413GenSource0005 :
    QuotientRankAtLeast (spanCodes [220, 32, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(220, 12), (32, 256), (2, 2), (1, 3)]
    (codeMat 177) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane413GenSource0006 :
    QuotientRankAtLeast (spanCodes [32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(32, 2), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane413GenSource0007 :
    QuotientRankAtLeast (spanCodes [32, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 12, 2, 1] [(32, 32), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit259_lb15_mono

theorem plane413GenSource0008 :
    QuotientRankAtLeast (spanCodes [32, 16, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(32, 2), (16, 1), (2, 8), (1, 32)]
    (codeMat 266) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane413GenSource0009 :
    QuotientRankAtLeast (spanCodes [32, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 12, 2, 1] [(32, 32), (20, 12), (2, 1), (1, 2)]
    (codeMat 273) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit259_lb15_mono

end QiushiMatmul
