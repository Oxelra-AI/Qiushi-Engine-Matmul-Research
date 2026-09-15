import FrozenRegistry.Btp261Data
import QiushiCertifiedTransport
import QiushiWcOrbit128Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane261BtpGenSource0030 :
    QuotientRankAtLeast (spanCodes [416, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(416, 480), (96, 96), (12, 12), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane261BtpGenSource0031 :
    QuotientRankAtLeast (spanCodes [420, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(420, 483), (96, 97), (12, 12), (2, 3), (1, 1)]
    (codeMat 337) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane261BtpGenSource0032 :
    QuotientRankAtLeast (spanCodes [432, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(432, 384), (96, 96), (12, 13), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane261BtpGenSource0033 :
    QuotientRankAtLeast (spanCodes [436, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(436, 386), (96, 108), (12, 13), (2, 2), (1, 1)]
    (codeMat 473) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

end QiushiMatmul
