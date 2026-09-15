import FrozenRegistry.Btp410Data
import QiushiCertifiedTransport
import QiushiGlobalOrbitUnused248Final
import QiushiGlobalOrbitUnused249Final
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane410BtpGenSource0060 :
    QuotientRankAtLeast (spanCodes [488, 4, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 4, 2, 1] [(488, 80), (4, 7), (2, 3), (1, 5)]
    (codeMat 273) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane249UnusedGen_lb14

theorem plane410BtpGenSource0061 :
    QuotientRankAtLeast (spanCodes [496, 4, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [80, 4, 2, 1] [(496, 80), (4, 7), (2, 5), (1, 3)]
    (codeMat 273) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane249UnusedGen_lb14

theorem plane410BtpGenSource0062 :
    QuotientRankAtLeast (spanCodes [504, 4, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [8, 4, 2, 1] [(504, 8), (4, 7), (2, 3), (1, 5)]
    (codeMat 305) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane248UnusedGen_lb14

end QiushiMatmul
