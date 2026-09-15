import QiushiPlane428GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiWcOrbit119Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane428GenSource0040 :
    QuotientRankAtLeast (spanCodes [268, 64, 32, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(268, 12), (64, 288), (32, 1), (16, 2), (1, 256)]
    (codeMat 106) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane428GenSource0041 :
    QuotientRankAtLeast (spanCodes [390, 72, 40, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(390, 45), (72, 288), (40, 2), (16, 3), (1, 256)]
    (codeMat 122) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane428GenSource0042 :
    QuotientRankAtLeast (spanCodes [398, 64, 32, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 32, 12, 2, 1] [(398, 12), (64, 288), (32, 2), (16, 3), (1, 256)]
    (codeMat 106) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit119_lb14_wc

theorem plane428GenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (130, 2), (66, 52), (34, 80), (16, 128), (4, 8), (1, 32)]
    (codeMat 141) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane428GenSource0044 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 11), (130, 2), (66, 52), (34, 208), (16, 128), (6, 8), (1, 32)]
    (codeMat 141) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane428GenSource0045 :
    QuotientRankAtLeast (spanCodes [264, 128, 74, 42, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(264, 198), (128, 130), (74, 21), (42, 208), (16, 128), (6, 32), (1, 40)]
    (codeMat 142) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane428GenSource0046 :
    QuotientRankAtLeast (spanCodes [264, 128, 74, 42, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(264, 68), (128, 130), (74, 21), (42, 80), (16, 128), (4, 32), (1, 40)]
    (codeMat 142) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane428GenSource0047 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 219), (132, 228), (68, 210), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 86) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane428GenSource0048 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 32, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 68), (132, 69), (64, 130), (32, 32), (16, 40), (14, 80), (1, 128)]
    (codeMat 85) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane428GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 132, 70, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (132, 237), (70, 82), (38, 240), (16, 40), (14, 208), (1, 128)]
    (codeMat 87) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
