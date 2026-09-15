import FrozenRegistry.Btp285Data
import QiushiCertifiedTransport
import QiushiStep81Qdim2Generated
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit165Dispatch
import QiushiWcOrbit166Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane285BtpGenSource0030 :
    QuotientRankAtLeast (spanCodes [384, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(384, 320), (96, 127), (20, 21), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane285BtpGenSource0031 :
    QuotientRankAtLeast (spanCodes [386, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(386, 322), (96, 127), (20, 21), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane285BtpGenSource0032 :
    QuotientRankAtLeast (spanCodes [388, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [290, 96, 20, 10, 1] [(388, 322), (96, 126), (20, 21), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit166_lb16_wc

theorem plane285BtpGenSource0033 :
    QuotientRankAtLeast (spanCodes [290, 160, 96, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 148, 80, 32, 12, 2, 1] [(290, 149), (160, 186), (96, 154), (16, 455), (10, 196), (4, 2), (1, 3)]
    (codeMat 225) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o16s2Span_lb

theorem plane285BtpGenSource0034 :
    QuotientRankAtLeast (spanCodes [390, 96, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 96, 20, 10, 1] [(390, 320), (96, 126), (20, 21), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit165_lb15_wc

theorem plane285BtpGenSource0035 :
    QuotientRankAtLeast (spanCodes [416, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(416, 383), (96, 127), (20, 21), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane285BtpGenSource0036 :
    QuotientRankAtLeast (spanCodes [418, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(418, 276), (96, 126), (20, 20), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane285BtpGenSource0037 :
    QuotientRankAtLeast (spanCodes [420, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(420, 276), (96, 127), (20, 20), (10, 11), (1, 1)]
    (codeMat 409) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane285BtpGenSource0038 :
    QuotientRankAtLeast (spanCodes [422, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(422, 383), (96, 126), (20, 21), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
