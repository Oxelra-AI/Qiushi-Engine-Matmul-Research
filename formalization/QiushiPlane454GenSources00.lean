import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiStep132Mono384From243
import QiushiStep133Mono393From243
import QiushiStep133Mono397From243
import QiushiStep133Mono400From243
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit322Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0000 :
    QuotientRankAtLeast (spanCodes [69, 37, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(69, 68), (37, 41), (20, 30), (10, 10)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane454GenSource0001 :
    QuotientRankAtLeast (spanCodes [135, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(135, 135), (96, 96), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane454GenSource0002 :
    QuotientRankAtLeast (spanCodes [162, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(162, 231), (96, 243), (20, 153), (10, 10)]
    (codeMat 331) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane454GenSource0003 :
    QuotientRankAtLeast (spanCodes [259, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 96, 20, 10] [(259, 259), (96, 96), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit400_lb17_mono

theorem plane454GenSource0004 :
    QuotientRankAtLeast (spanCodes [294, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(294, 274), (96, 328), (20, 20), (10, 30)]
    (codeMat 403) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane454GenSource0005 :
    QuotientRankAtLeast (spanCodes [388, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(388, 147), (96, 20), (20, 153), (10, 126)]
    (codeMat 500) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane454GenSource0006 :
    QuotientRankAtLeast (spanCodes [417, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(417, 249), (96, 135), (20, 237), (10, 243)]
    (codeMat 501) (codeMat 467) (codeMat 339) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane454GenSource0007 :
    QuotientRankAtLeast (spanCodes [423, 96, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(423, 318), (96, 319), (20, 170), (10, 414)]
    (codeMat 285) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane454GenSource0008 :
    QuotientRankAtLeast (spanCodes [68, 36, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 68), (36, 32), (20, 31), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane454GenSource0009 :
    QuotientRankAtLeast (spanCodes [69, 37, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(69, 80), (37, 11), (20, 53), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

end QiushiMatmul
