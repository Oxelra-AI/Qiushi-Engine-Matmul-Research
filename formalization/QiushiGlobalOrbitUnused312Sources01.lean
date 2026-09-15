import QiushiGlobalOrbitUnused312Data
import QiushiCertifiedTransport
import QiushiBranch262Dispatch
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit35FP
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit218Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane312UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [306, 176, 96, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(306, 350), (176, 175), (96, 133), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane312UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [304, 178, 96, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(304, 278), (178, 175), (96, 132), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane312UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [310, 180, 96, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(310, 287), (180, 238), (96, 133), (10, 11), (1, 1)]
    (codeMat 465) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane312UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [308, 182, 96, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(308, 343), (182, 238), (96, 132), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane312UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [256, 130, 96, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (130, 130), (96, 28), (10, 97), (4, 1), (1, 8)]
    (codeMat 169) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane312UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [386, 82, 50, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(386, 150), (82, 232), (50, 20), (10, 29), (6, 2), (1, 3)]
    (codeMat 473) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane312UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [386, 68, 36, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(386, 291), (68, 316), (36, 365), (20, 364), (10, 296), (1, 32)]
    (codeMat 114) (codeMat 444) (codeMat 110) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109wc156s1Dispatch

theorem plane312UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [272, 146, 64, 32, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(272, 164), (146, 45), (64, 2), (32, 438), (10, 15), (1, 1)]
    (codeMat 417) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_262_row11_qr

theorem plane312UnusedGenSource0018 :
    QuotientRankAtLeast (spanCodes [292, 164, 96, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(292, 511), (164, 255), (96, 77), (16, 9), (8, 1), (2, 18), (1, 2)]
    (codeMat 266) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane312UnusedGenSource0019 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 119), (128, 9), (66, 118), (34, 245), (20, 413), (10, 246), (1, 384)]
    (codeMat 500) (codeMat 342) (codeMat 215) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
