import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane298GenFinal
import QiushiPlane324GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0130 :
    QuotientRankAtLeast (spanCodes [84, 48, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(84, 116), (48, 2), (8, 1), (2, 32)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane487GenSource0131 :
    QuotientRankAtLeast (spanCodes [65, 32, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(65, 384), (32, 32), (21, 10), (10, 43)]
    (codeMat 339) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0132 :
    QuotientRankAtLeast (spanCodes [67, 34, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(67, 427), (34, 42), (23, 33), (10, 43)]
    (codeMat 474) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0133 :
    QuotientRankAtLeast (spanCodes [81, 48, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [196, 36, 16, 1] [(81, 240), (48, 16), (10, 53), (5, 36)]
    (codeMat 467) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane324Gen_lb16

theorem plane487GenSource0134 :
    QuotientRankAtLeast (spanCodes [64, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(64, 384), (34, 11), (20, 10), (10, 43)]
    (codeMat 275) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0135 :
    QuotientRankAtLeast (spanCodes [84, 53, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(84, 85), (53, 34), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane487GenSource0136 :
    QuotientRankAtLeast (spanCodes [128, 84, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(128, 2), (84, 84), (8, 32), (2, 1)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane487GenSource0137 :
    QuotientRankAtLeast (spanCodes [130, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(130, 1), (83, 10), (10, 43), (7, 384)]
    (codeMat 501) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0138 :
    QuotientRankAtLeast (spanCodes [128, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(128, 1), (82, 10), (10, 43), (6, 384)]
    (codeMat 444) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0139 :
    QuotientRankAtLeast (spanCodes [130, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(130, 32), (80, 10), (10, 43), (4, 384)]
    (codeMat 358) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

end QiushiMatmul
