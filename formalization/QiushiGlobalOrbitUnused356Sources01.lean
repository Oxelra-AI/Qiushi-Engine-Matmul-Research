import QiushiGlobalOrbitUnused356Data
import QiushiCertifiedTransport
import QiushiBranch262Dispatch
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit35FP
import QiushiWcOrbit165Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane356UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [290, 166, 96, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(290, 327), (166, 338), (96, 352), (20, 509), (1, 1)]
    (codeMat 417) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane356UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [290, 170, 96, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(290, 39), (170, 175), (96, 352), (20, 508), (1, 1)]
    (codeMat 305) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane356UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [290, 172, 96, 20, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(290, 43), (172, 143), (96, 507), (20, 373), (1, 32)]
    (codeMat 334) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane356UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [290, 174, 96, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(290, 97), (174, 298), (96, 126), (20, 308), (1, 288)]
    (codeMat 94) (codeMat 348) (codeMat 125) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane356UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [290, 96, 16, 8, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(290, 96), (96, 22), (16, 128), (8, 2), (4, 8), (1, 1)]
    (codeMat 401) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane356UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [262, 68, 36, 20, 8, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 224), (68, 28), (36, 8), (20, 136), (8, 2), (1, 3)]
    (codeMat 275) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane356UnusedGenSource0016 :
    QuotientRankAtLeast (spanCodes [260, 70, 38, 20, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 45), (70, 133), (38, 166), (20, 306), (14, 134), (1, 2)]
    (codeMat 143) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step113_262_row11_qr

theorem plane356UnusedGenSource0017 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 511), (128, 128), (96, 255), (20, 21), (12, 28), (2, 2), (1, 3)]
    (codeMat 281) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane356UnusedGenSource0018 :
    QuotientRankAtLeast (spanCodes [288, 132, 96, 20, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(288, 384), (132, 150), (96, 232), (20, 22), (12, 30), (2, 2), (1, 3)]
    (codeMat 401) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane356UnusedGenSource0019 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 8), (128, 3), (68, 208), (36, 32), (20, 22), (2, 2), (1, 128)]
    (codeMat 205) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
