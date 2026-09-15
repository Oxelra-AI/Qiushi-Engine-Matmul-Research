import QiushiGlobalOrbitUnused398Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit35FP
import QiushiStep99Orbit67Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit239Dispatch
import QiushiWcOrbit242Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane398UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [290, 161, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 164, 68, 19, 10] [(290, 326), (161, 174), (96, 19), (20, 68), (10, 332)]
    (codeMat 226) (codeMat 143) (codeMat 482) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit242_lb16_wc

theorem plane398UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [291, 161, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 19, 10] [(291, 19), (161, 277), (96, 437), (20, 322), (10, 488)]
    (codeMat 335) (codeMat 204) (codeMat 114) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit239_lb16_wc

theorem plane398UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [293, 161, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(293, 136), (161, 431), (96, 137), (20, 252), (10, 306)]
    (codeMat 445) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane398UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [294, 161, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 164, 68, 19, 10] [(294, 78), (161, 234), (96, 488), (20, 437), (10, 326)]
    (codeMat 359) (codeMat 354) (codeMat 142) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit242_lb16_wc

theorem plane398UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [160, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(160, 224), (96, 96), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane398UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [161, 96, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(161, 253), (96, 235), (17, 11), (9, 8), (5, 130), (3, 2)]
    (codeMat 331) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane398UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [291, 161, 96, 19, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 164, 68, 16, 10, 1] [(291, 26), (161, 345), (96, 434), (19, 284), (10, 487), (7, 27)]
    (codeMat 183) (codeMat 207) (codeMat 370) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit67_lb15_unconditional

theorem plane398UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (129, 160), (64, 16), (32, 1), (20, 68), (8, 8), (2, 256)]
    (codeMat 98) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane398UnusedGenSource0018 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 105), (129, 227), (64, 511), (32, 1), (16, 3), (10, 31), (4, 8)]
    (codeMat 458) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane398UnusedGenSource0019 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (130, 2), (67, 22), (35, 224), (16, 3), (10, 31), (4, 256)]
    (codeMat 111) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
