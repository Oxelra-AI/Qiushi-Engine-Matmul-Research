import QiushiGlobalOrbitUnused88Data
import QiushiCertifiedTransport
import QiushiOrbit25FP
import QiushiOrbit5FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane88UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [416, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(416, 344), (80, 80), (8, 8), (4, 6), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane88UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [432, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(432, 256), (80, 88), (8, 8), (4, 6), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane88UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [160, 64, 16, 8, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(160, 160), (64, 64), (16, 16), (8, 8), (4, 4), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

end QiushiMatmul
