import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane274GenFinal
import QiushiPlane276GenFinal
import QiushiPlane298GenFinal
import QiushiPlane324GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0140 :
    QuotientRankAtLeast (spanCodes [133, 84, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(133, 119), (84, 85), (9, 32), (3, 1)]
    (codeMat 241) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane487GenSource0141 :
    QuotientRankAtLeast (spanCodes [144, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(144, 1), (80, 33), (10, 43), (4, 384)]
    (codeMat 302) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0142 :
    QuotientRankAtLeast (spanCodes [146, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(146, 32), (82, 33), (10, 43), (6, 384)]
    (codeMat 500) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0143 :
    QuotientRankAtLeast (spanCodes [128, 67, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [196, 36, 16, 1] [(128, 16), (67, 17), (23, 240), (10, 53)]
    (codeMat 485) (codeMat 317) (codeMat 285) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane324Gen_lb16

theorem plane487GenSource0144 :
    QuotientRankAtLeast (spanCodes [130, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 2, 1] [(130, 2), (65, 1), (21, 160), (10, 80)]
    (codeMat 141) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274Gen_lb16

theorem plane487GenSource0145 :
    QuotientRankAtLeast (spanCodes [144, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(144, 32), (83, 33), (10, 43), (7, 384)]
    (codeMat 445) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0146 :
    QuotientRankAtLeast (spanCodes [146, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(146, 1), (81, 33), (10, 43), (5, 384)]
    (codeMat 359) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane487GenSource0147 :
    QuotientRankAtLeast (spanCodes [148, 84, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(148, 119), (84, 117), (9, 32), (3, 1)]
    (codeMat 225) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane487GenSource0148 :
    QuotientRankAtLeast (spanCodes [256, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(256, 1), (80, 96), (10, 272), (4, 2)]
    (codeMat 140) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane487GenSource0149 :
    QuotientRankAtLeast (spanCodes [260, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(260, 3), (65, 2), (21, 96), (10, 272)]
    (codeMat 85) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

end QiushiMatmul
