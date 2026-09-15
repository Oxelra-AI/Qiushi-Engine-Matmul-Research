import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane152GenFinal
import QiushiPlane276GenFinal
import QiushiPlane278GenFinal
import QiushiPlane298GenFinal
import QiushiWcOrbit156Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0110 :
    QuotientRankAtLeast (spanCodes [258, 35, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 112), (35, 33), (19, 30), (10, 43), (7, 32)]
    (codeMat 267) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane489GenSource0111 :
    QuotientRankAtLeast (spanCodes [257, 101, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(257, 43), (101, 10), (9, 1), (3, 384)]
    (codeMat 499) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane489GenSource0112 :
    QuotientRankAtLeast (spanCodes [258, 180, 101, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(258, 97), (180, 96), (101, 368), (10, 274)]
    (codeMat 239) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane489GenSource0113 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 101), (129, 33), (65, 32), (19, 30), (10, 53)]
    (codeMat 372) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane489GenSource0114 :
    QuotientRankAtLeast (spanCodes [258, 149, 86, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [164, 96, 16, 10, 1] [(258, 196), (149, 191), (86, 190), (39, 96), (10, 112)]
    (codeMat 93) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane152Gen_lb16

theorem plane489GenSource0115 :
    QuotientRankAtLeast (spanCodes [258, 197, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(258, 97), (197, 96), (53, 272), (10, 274)]
    (codeMat 93) (codeMat 415) (codeMat 253) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane489GenSource0116 :
    QuotientRankAtLeast (spanCodes [258, 146, 101, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(258, 306), (146, 2), (101, 97), (10, 338)]
    (codeMat 183) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane489GenSource0117 :
    QuotientRankAtLeast (spanCodes [258, 180, 67, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(258, 96), (180, 97), (67, 336), (10, 338)]
    (codeMat 111) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane489GenSource0118 :
    QuotientRankAtLeast (spanCodes [258, 194, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(258, 306), (194, 304), (53, 97), (10, 96)]
    (codeMat 99) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

theorem plane489GenSource0119 :
    QuotientRankAtLeast (spanCodes [258, 197, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 96, 2, 1] [(258, 96), (197, 97), (50, 304), (10, 306)]
    (codeMat 85) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane278Gen_lb16

end QiushiMatmul
