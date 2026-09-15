import QiushiPlane480GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit252From101
import QiushiMonoOrbit89From23
import QiushiOrbit23FP
import QiushiWcOrbit111Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane480GenSource0140 :
    QuotientRankAtLeast (spanCodes [128, 64, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(128, 1), (64, 8), (16, 2), (1, 32)]
    (codeMat 84) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0141 :
    QuotientRankAtLeast (spanCodes [130, 64, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(130, 1), (64, 40), (16, 2), (1, 32)]
    (codeMat 85) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0142 :
    QuotientRankAtLeast (spanCodes [128, 72, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(128, 3), (72, 8), (16, 2), (1, 32)]
    (codeMat 86) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0143 :
    QuotientRankAtLeast (spanCodes [130, 72, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 8, 2, 1] [(130, 3), (72, 40), (16, 2), (1, 32)]
    (codeMat 87) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit252_lb15_mono

theorem plane480GenSource0144 :
    QuotientRankAtLeast (spanCodes [260, 130, 70, 16, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 8, 2, 1] [(260, 9), (130, 1), (70, 352), (16, 2), (1, 256)]
    (codeMat 85) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit111_lb14_wc

theorem plane480GenSource0145 :
    QuotientRankAtLeast (spanCodes [256, 32, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(256, 4), (32, 1), (16, 8), (4, 2), (1, 128)]
    (codeMat 266) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane480GenSource0146 :
    QuotientRankAtLeast (spanCodes [260, 68, 32, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(260, 216), (68, 208), (32, 3), (16, 4), (8, 2), (1, 128)]
    (codeMat 98) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0147 :
    QuotientRankAtLeast (spanCodes [256, 68, 32, 16, 8, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(256, 8), (68, 80), (32, 1), (16, 4), (8, 2), (1, 128)]
    (codeMat 98) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane480GenSource0148 :
    QuotientRankAtLeast (spanCodes [320, 40, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 8, 4, 2, 1] [(320, 4), (40, 1), (16, 8), (4, 128), (1, 130)]
    (codeMat 266) (codeMat 337) (codeMat 337) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit89_lb12_mono

theorem plane480GenSource0149 :
    QuotientRankAtLeast (spanCodes [288, 160, 16, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(288, 216), (160, 208), (16, 128), (4, 3), (2, 2), (1, 4)]
    (codeMat 161) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

end QiushiMatmul
