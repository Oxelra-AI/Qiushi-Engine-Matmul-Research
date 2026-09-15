import FrozenRegistry.Btp260Data
import QiushiCertifiedTransport
import QiushiMonoOrbit124From35T
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane260BtpGenSource0030 :
    QuotientRankAtLeast (spanCodes [420, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(420, 350), (80, 80), (12, 14), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane260BtpGenSource0031 :
    QuotientRankAtLeast (spanCodes [432, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(432, 256), (80, 80), (12, 15), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

theorem plane260BtpGenSource0032 :
    QuotientRankAtLeast (spanCodes [436, 80, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 12, 2, 1] [(436, 259), (80, 83), (12, 14), (2, 3), (1, 1)]
    (codeMat 473) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit124_lb15_mono

end QiushiMatmul
