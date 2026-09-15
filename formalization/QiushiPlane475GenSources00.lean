import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiStep133Mono397From243
import QiushiStep133Mono409From247T
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0000 :
    QuotientRankAtLeast (spanCodes [165, 96, 21, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(165, 116), (96, 243), (21, 153), (10, 10)]
    (codeMat 459) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane475GenSource0001 :
    QuotientRankAtLeast (spanCodes [131, 70, 38, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(131, 30), (70, 237), (38, 147), (10, 10)]
    (codeMat 474) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane475GenSource0002 :
    QuotientRankAtLeast (spanCodes [150, 83, 51, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(150, 96), (83, 30), (51, 153), (10, 10)]
    (codeMat 465) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane475GenSource0003 :
    QuotientRankAtLeast (spanCodes [257, 165, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(257, 10), (165, 141), (96, 20), (10, 96)]
    (codeMat 161) (codeMat 140) (codeMat 98) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane475GenSource0004 :
    QuotientRankAtLeast (spanCodes [276, 165, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 165, 96, 10] [(276, 10), (165, 465), (96, 276), (10, 96)]
    (codeMat 85) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit409_lb17_mono

theorem plane475GenSource0005 :
    QuotientRankAtLeast (spanCodes [295, 165, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(295, 135), (165, 116), (96, 153), (10, 96)]
    (codeMat 242) (codeMat 348) (codeMat 125) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane475GenSource0006 :
    QuotientRankAtLeast (spanCodes [306, 165, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(306, 147), (165, 249), (96, 237), (10, 96)]
    (codeMat 107) (codeMat 500) (codeMat 94) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane475GenSource0007 :
    QuotientRankAtLeast (spanCodes [132, 65, 33, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 132), (65, 32), (33, 341), (22, 133), (10, 42)]
    (codeMat 335) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane475GenSource0008 :
    QuotientRankAtLeast (spanCodes [259, 162, 96, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 33), (162, 316), (96, 278), (10, 133), (7, 1)]
    (codeMat 233) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane475GenSource0009 :
    QuotientRankAtLeast (spanCodes [259, 160, 96, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 96), (160, 276), (96, 20), (10, 127), (5, 1)]
    (codeMat 305) (codeMat 187) (codeMat 229) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
