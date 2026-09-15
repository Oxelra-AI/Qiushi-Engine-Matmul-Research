import FrozenRegistry.Btp265Data
import QiushiCertifiedTransport
import QiushiWcOrbit132Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane265BtpGenSource0030 :
    QuotientRankAtLeast (spanCodes [272, 244, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(272, 414), (244, 172), (12, 14), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

end QiushiMatmul
