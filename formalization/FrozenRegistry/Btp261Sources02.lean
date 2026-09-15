import FrozenRegistry.Btp261Data
import QiushiCertifiedTransport
import QiushiMonoOrbit126From55
import QiushiOrbit23FP
import QiushiWcOrbit127Dispatch
import QiushiWcOrbit128Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane261BtpGenSource0020 :
    QuotientRankAtLeast (spanCodes [276, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 12, 2, 1] [(276, 284), (96, 96), (12, 12), (2, 3), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit127_lb15_wc

theorem plane261BtpGenSource0021 :
    QuotientRankAtLeast (spanCodes [288, 96, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 12, 2, 1] [(288, 365), (96, 109), (12, 12), (2, 3), (1, 1)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit126_lb14_mono

theorem plane261BtpGenSource0022 :
    QuotientRankAtLeast (spanCodes [288, 96, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(288, 216), (96, 88), (8, 8), (4, 3), (2, 6), (1, 1)]
    (codeMat 273) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane261BtpGenSource0023 :
    QuotientRankAtLeast (spanCodes [292, 96, 12, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 12, 2, 1] [(292, 365), (96, 108), (12, 12), (2, 3), (1, 1)]
    (codeMat 345) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit126_lb14_mono

theorem plane261BtpGenSource0024 :
    QuotientRankAtLeast (spanCodes [304, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 12, 2, 1] [(304, 383), (96, 109), (12, 12), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit127_lb15_wc

theorem plane261BtpGenSource0025 :
    QuotientRankAtLeast (spanCodes [308, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 12, 2, 1] [(308, 371), (96, 109), (12, 12), (2, 3), (1, 1)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit127_lb15_wc

theorem plane261BtpGenSource0026 :
    QuotientRankAtLeast (spanCodes [384, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(384, 384), (96, 96), (12, 12), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane261BtpGenSource0027 :
    QuotientRankAtLeast (spanCodes [388, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(388, 386), (96, 97), (12, 12), (2, 2), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane261BtpGenSource0028 :
    QuotientRankAtLeast (spanCodes [400, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(400, 483), (96, 108), (12, 13), (2, 3), (1, 1)]
    (codeMat 473) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane261BtpGenSource0029 :
    QuotientRankAtLeast (spanCodes [404, 96, 12, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(404, 493), (96, 96), (12, 13), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

end QiushiMatmul
