import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane269GenFinal
import QiushiPlane292GenFinal
import QiushiPlane298GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0120 :
    QuotientRankAtLeast (spanCodes [67, 16, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(67, 138), (16, 1), (10, 10), (7, 32)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0121 :
    QuotientRankAtLeast (spanCodes [67, 17, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(67, 138), (17, 11), (10, 10), (6, 32)]
    (codeMat 459) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0122 :
    QuotientRankAtLeast (spanCodes [64, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(64, 2), (20, 297), (9, 1), (3, 32)]
    (codeMat 99) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane487GenSource0123 :
    QuotientRankAtLeast (spanCodes [65, 21, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(65, 2), (21, 264), (8, 1), (2, 32)]
    (codeMat 106) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane487GenSource0124 :
    QuotientRankAtLeast (spanCodes [84, 32, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(84, 84), (32, 2), (8, 1), (2, 32)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane487GenSource0125 :
    QuotientRankAtLeast (spanCodes [84, 36, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(84, 117), (36, 3), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane487GenSource0126 :
    QuotientRankAtLeast (spanCodes [64, 36, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(64, 384), (36, 32), (20, 33), (10, 43)]
    (codeMat 282) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0127 :
    QuotientRankAtLeast (spanCodes [67, 39, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(67, 427), (39, 42), (23, 10), (10, 43)]
    (codeMat 467) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0128 :
    QuotientRankAtLeast (spanCodes [66, 36, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(66, 427), (36, 1), (22, 10), (10, 43)]
    (codeMat 403) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0129 :
    QuotientRankAtLeast (spanCodes [65, 39, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(65, 384), (39, 11), (21, 33), (10, 43)]
    (codeMat 346) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

end QiushiMatmul
