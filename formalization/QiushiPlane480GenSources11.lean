import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiPlane269GenFinal
import QiushiWcOrbit281Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0110 :
    QuotientRankAtLeast (spanCodes [130, 16, 14, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(130, 2), (16, 1), (14, 264), (1, 32)]
    (codeMat 106) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane480GenSource0111 :
    QuotientRankAtLeast (spanCodes [260, 68, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(260, 27), (68, 26), (16, 256), (1, 16)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0112 :
    QuotientRankAtLeast (spanCodes [256, 68, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(256, 1), (68, 10), (16, 256), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0113 :
    QuotientRankAtLeast (spanCodes [292, 76, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(292, 27), (76, 26), (16, 256), (1, 16)]
    (codeMat 142) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0114 :
    QuotientRankAtLeast (spanCodes [288, 76, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(288, 1), (76, 10), (16, 256), (1, 16)]
    (codeMat 142) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0115 :
    QuotientRankAtLeast (spanCodes [288, 160, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(288, 27), (160, 26), (16, 16), (1, 256)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0116 :
    QuotientRankAtLeast (spanCodes [292, 162, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(292, 27), (162, 26), (16, 16), (1, 256)]
    (codeMat 85) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0117 :
    QuotientRankAtLeast (spanCodes [256, 160, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(256, 1), (160, 10), (16, 16), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0118 :
    QuotientRankAtLeast (spanCodes [260, 162, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(260, 1), (162, 10), (16, 16), (1, 256)]
    (codeMat 85) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane480GenSource0119 :
    QuotientRankAtLeast (spanCodes [360, 168, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(360, 27), (168, 26), (16, 16), (1, 256)]
    (codeMat 84) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

end QiushiMatmul
