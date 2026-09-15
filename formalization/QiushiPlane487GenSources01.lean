import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane456GenFinal
import QiushiPlane461GenFinal
import QiushiPlane463GenFinal
import QiushiPlane467GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0010 :
    QuotientRankAtLeast (spanCodes [131, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(131, 10), (84, 161), (10, 20)]
    (codeMat 141) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane487GenSource0011 :
    QuotientRankAtLeast (spanCodes [132, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(132, 191), (84, 161), (10, 20)]
    (codeMat 207) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane487GenSource0012 :
    QuotientRankAtLeast (spanCodes [135, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(135, 191), (84, 161), (10, 20)]
    (codeMat 206) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane487GenSource0013 :
    QuotientRankAtLeast (spanCodes [145, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(145, 10), (84, 181), (10, 20)]
    (codeMat 142) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane487GenSource0014 :
    QuotientRankAtLeast (spanCodes [147, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(147, 10), (84, 181), (10, 20)]
    (codeMat 143) (codeMat 309) (codeMat 309) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane487GenSource0015 :
    QuotientRankAtLeast (spanCodes [149, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(149, 191), (84, 181), (10, 20)]
    (codeMat 204) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane487GenSource0016 :
    QuotientRankAtLeast (spanCodes [150, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(150, 191), (84, 181), (10, 20)]
    (codeMat 205) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

theorem plane487GenSource0017 :
    QuotientRankAtLeast (spanCodes [161, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [179, 68, 10] [(161, 253), (84, 179), (10, 10)]
    (codeMat 267) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane463Gen_lb18

theorem plane487GenSource0018 :
    QuotientRankAtLeast (spanCodes [162, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [162, 68, 10] [(162, 162), (84, 230), (10, 10)]
    (codeMat 275) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane461Gen_lb18

theorem plane487GenSource0019 :
    QuotientRankAtLeast (spanCodes [163, 84, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [163, 84, 10] [(163, 247), (84, 163), (10, 10)]
    (codeMat 267) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane467Gen_lb18

end QiushiMatmul
