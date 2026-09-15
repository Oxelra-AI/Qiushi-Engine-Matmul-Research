import QiushiGlobalOrbitUnused92Data
import QiushiCertifiedTransport
import QiushiOrbit8Closed
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane92UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [264, 152, 80, 56, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 64, 8, 4, 2, 1] [(264, 224), (152, 400), (80, 304), (56, 8), (4, 3), (2, 6), (1, 4)]
    (codeMat 273) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit8_lb9

end QiushiMatmul
