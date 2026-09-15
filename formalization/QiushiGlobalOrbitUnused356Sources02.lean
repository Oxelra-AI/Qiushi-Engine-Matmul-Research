import QiushiGlobalOrbitUnused356Data
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane356UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [268, 132, 76, 44, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(268, 150), (132, 113), (76, 20), (44, 160), (20, 120), (2, 8), (1, 32)]
    (codeMat 207) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane356UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 64, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 68), (64, 32), (32, 2), (16, 128), (10, 80), (4, 1), (1, 8)]
    (codeMat 273) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane356UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (128, 8), (66, 81), (34, 20), (16, 32), (4, 2), (1, 130)]
    (codeMat 140) (codeMat 85) (codeMat 340) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane356UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 139), (130, 9), (64, 2), (32, 360), (20, 245), (10, 30), (1, 3)]
    (codeMat 485) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane356UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 278), (132, 404), (64, 256), (32, 360), (20, 413), (10, 374), (1, 384)]
    (codeMat 302) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane356UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (128, 9), (66, 118), (34, 30), (20, 29), (10, 374), (1, 384)]
    (codeMat 444) (codeMat 114) (codeMat 204) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane356UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (134, 255), (66, 28), (34, 374), (20, 246), (10, 30), (1, 3)]
    (codeMat 375) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
