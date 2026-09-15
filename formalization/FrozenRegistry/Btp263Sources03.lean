import FrozenRegistry.Btp263Data
import QiushiCertifiedTransport
import QiushiWcOrbit132Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane263BtpGenSource0030 :
    QuotientRankAtLeast (spanCodes [372, 160, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(372, 318), (160, 175), (12, 12), (2, 2), (1, 1)]
    (codeMat 345) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

end QiushiMatmul
