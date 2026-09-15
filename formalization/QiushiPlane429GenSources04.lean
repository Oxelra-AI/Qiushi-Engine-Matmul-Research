import QiushiPlane429GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit78Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane429GenSource0040 :
    QuotientRankAtLeast (spanCodes [264, 128, 64, 34, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 20), (128, 1), (64, 2), (34, 96), (16, 8), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0041 :
    QuotientRankAtLeast (spanCodes [294, 134, 98, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(294, 255), (134, 480), (98, 431), (16, 260), (10, 69), (1, 320)]
    (codeMat 107) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane429GenSource0042 :
    QuotientRankAtLeast (spanCodes [268, 130, 64, 34, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(268, 20), (130, 1), (64, 130), (34, 96), (16, 8), (1, 128)]
    (codeMat 85) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0043 :
    QuotientRankAtLeast (spanCodes [386, 74, 40, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(386, 96), (74, 118), (40, 130), (16, 128), (6, 8), (1, 9)]
    (codeMat 273) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0044 :
    QuotientRankAtLeast (spanCodes [262, 130, 72, 42, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 118), (130, 9), (72, 130), (42, 96), (16, 8), (1, 128)]
    (codeMat 87) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0045 :
    QuotientRankAtLeast (spanCodes [392, 66, 32, 16, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(392, 20), (66, 97), (32, 128), (16, 130), (6, 1), (1, 8)]
    (codeMat 273) (codeMat 394) (codeMat 330) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane429GenSource0046 :
    QuotientRankAtLeast (spanCodes [258, 132, 98, 16, 12, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 96, 20, 10, 1] [(258, 402), (132, 274), (98, 159), (16, 390), (12, 97), (1, 365)]
    (codeMat 351) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit78_lb14_wc

theorem plane429GenSource0047 :
    QuotientRankAtLeast (spanCodes [258, 136, 72, 42, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 487), (136, 324), (72, 1), (42, 416), (16, 256), (6, 24), (1, 8)]
    (codeMat 142) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane429GenSource0048 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (128, 1), (66, 68), (32, 16), (16, 8), (12, 160), (1, 256)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane429GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 326), (68, 324), (38, 424), (16, 432), (10, 160), (1, 256)]
    (codeMat 92) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
