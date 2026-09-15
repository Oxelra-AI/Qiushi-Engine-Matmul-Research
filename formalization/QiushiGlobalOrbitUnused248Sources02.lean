import QiushiGlobalOrbitUnused248Data
import QiushiCertifiedTransport
import QiushiOrbit5FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane248UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(256, 16), (160, 160), (64, 2), (8, 4), (4, 8), (2, 64), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

theorem plane248UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [272, 160, 64, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(272, 176), (160, 160), (64, 6), (8, 4), (4, 72), (2, 64), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

theorem plane248UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [304, 176, 64, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(304, 176), (176, 160), (64, 2), (8, 4), (4, 72), (2, 64), (1, 1)]
    (codeMat 161) (codeMat 417) (codeMat 177) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

end QiushiMatmul
