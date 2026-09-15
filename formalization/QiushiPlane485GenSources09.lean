import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane269GenFinal
import QiushiPlane324GenFinal
import QiushiPlane447GenFinal
import QiushiStep126Mono251From96
import QiushiWcOrbit264Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0090 :
    QuotientRankAtLeast (spanCodes [448, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [306, 160, 1] [(448, 1), (20, 160), (10, 402)]
    (codeMat 84) (codeMat 233) (codeMat 233) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane447Gen_lb17

theorem plane485GenSource0091 :
    QuotientRankAtLeast (spanCodes [20, 8, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [20, 8, 2, 1] [(20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit251_lb16_mono

theorem plane485GenSource0092 :
    QuotientRankAtLeast (spanCodes [34, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [20, 8, 2, 1] [(34, 20), (17, 30), (10, 29), (5, 8)]
    (codeMat 267) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit251_lb16_mono

theorem plane485GenSource0093 :
    QuotientRankAtLeast (spanCodes [64, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(64, 2), (20, 264), (8, 1), (2, 32)]
    (codeMat 98) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0094 :
    QuotientRankAtLeast (spanCodes [65, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(65, 2), (20, 297), (9, 1), (3, 32)]
    (codeMat 107) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0095 :
    QuotientRankAtLeast (spanCodes [64, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(64, 2), (20, 297), (9, 1), (3, 32)]
    (codeMat 99) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0096 :
    QuotientRankAtLeast (spanCodes [65, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(65, 2), (20, 264), (8, 1), (2, 32)]
    (codeMat 106) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0097 :
    QuotientRankAtLeast (spanCodes [128, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(128, 2), (20, 12), (8, 256), (2, 1)]
    (codeMat 161) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane485GenSource0098 :
    QuotientRankAtLeast (spanCodes [130, 66, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [196, 36, 16, 1] [(130, 1), (66, 17), (20, 197), (10, 53)]
    (codeMat 421) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane324Gen_lb16

theorem plane485GenSource0099 :
    QuotientRankAtLeast (spanCodes [256, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(256, 2), (16, 32), (10, 264), (4, 1)]
    (codeMat 161) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

end QiushiMatmul
