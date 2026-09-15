import QiushiPlane456LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit310From196T
import QiushiMonoOrbit370From196
import QiushiOrbit101FP
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456LowerGenSource0040 :
    QuotientRankAtLeast (spanCodes [257, 161, 70, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(257, 400), (161, 106), (70, 96), (20, 383), (10, 228)]
    (codeMat 110) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane456LowerGenSource0041 :
    QuotientRankAtLeast (spanCodes [256, 161, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(256, 1), (161, 142), (96, 10), (20, 97), (10, 276)]
    (codeMat 340) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane456LowerGenSource0042 :
    QuotientRankAtLeast (spanCodes [258, 161, 99, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(258, 133), (161, 239), (99, 107), (20, 466), (10, 310)]
    (codeMat 124) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane456LowerGenSource0043 :
    QuotientRankAtLeast (spanCodes [354, 161, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(354, 181), (161, 494), (20, 160), (10, 180)]
    (codeMat 158) (codeMat 465) (codeMat 465) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane456LowerGenSource0044 :
    QuotientRankAtLeast (spanCodes [256, 161, 99, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(256, 1), (161, 358), (99, 157), (20, 399), (10, 252)]
    (codeMat 444) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane456LowerGenSource0045 :
    QuotientRankAtLeast (spanCodes [256, 161, 100, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(256, 256), (161, 116), (100, 96), (20, 383), (10, 362)]
    (codeMat 271) (codeMat 474) (codeMat 395) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane456LowerGenSource0046 :
    QuotientRankAtLeast (spanCodes [256, 161, 101, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(256, 1), (161, 107), (101, 97), (20, 497), (10, 287)]
    (codeMat 492) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane456LowerGenSource0047 :
    QuotientRankAtLeast (spanCodes [259, 161, 101, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 11), (161, 107), (101, 97), (20, 408), (10, 374)]
    (codeMat 421) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456LowerGenSource0048 :
    QuotientRankAtLeast (spanCodes [359, 161, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 10, 1] [(359, 305), (161, 106), (20, 336), (10, 304)]
    (codeMat 95) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit310_lb16_mono

theorem plane456LowerGenSource0049 :
    QuotientRankAtLeast (spanCodes [161, 16, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(161, 84), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

end QiushiMatmul
