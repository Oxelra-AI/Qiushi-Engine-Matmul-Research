import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0040 :
    QuotientRankAtLeast (spanCodes [257, 163, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(257, 363), (163, 372), (96, 373), (20, 287), (10, 126)]
    (codeMat 501) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane454GenSource0041 :
    QuotientRankAtLeast (spanCodes [290, 128, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 10), (128, 32), (96, 310), (20, 43), (10, 408)]
    (codeMat 311) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane454GenSource0042 :
    QuotientRankAtLeast (spanCodes [293, 135, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(293, 440), (135, 316), (96, 408), (20, 133), (10, 175)]
    (codeMat 351) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane454GenSource0043 :
    QuotientRankAtLeast (spanCodes [261, 166, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(261, 274), (166, 399), (96, 137), (20, 252), (10, 507)]
    (codeMat 102) (codeMat 253) (codeMat 415) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane454GenSource0044 :
    QuotientRankAtLeast (spanCodes [384, 67, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(384, 32), (67, 132), (35, 383), (20, 341), (10, 133)]
    (codeMat 271) (codeMat 423) (codeMat 181) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane454GenSource0045 :
    QuotientRankAtLeast (spanCodes [418, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(418, 276), (96, 126), (20, 20), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane454GenSource0046 :
    QuotientRankAtLeast (spanCodes [290, 134, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 33), (134, 42), (96, 164), (20, 43), (10, 435)]
    (codeMat 423) (codeMat 111) (codeMat 412) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane454GenSource0047 :
    QuotientRankAtLeast (spanCodes [386, 70, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(386, 164), (70, 301), (38, 262), (20, 386), (10, 133)]
    (codeMat 114) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane454GenSource0048 :
    QuotientRankAtLeast (spanCodes [256, 165, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(256, 1), (165, 142), (96, 11), (20, 97), (10, 284)]
    (codeMat 340) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane454GenSource0049 :
    QuotientRankAtLeast (spanCodes [259, 166, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 507), (166, 137), (96, 398), (20, 274), (10, 20)]
    (codeMat 94) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

end QiushiMatmul
