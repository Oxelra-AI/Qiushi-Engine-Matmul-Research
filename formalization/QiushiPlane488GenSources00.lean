import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane455GenFinal
import QiushiPlane456GenFinal
import QiushiStep108Orbit450Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0000 :
    QuotientRankAtLeast (spanCodes [96, 19, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 19, 10] [(96, 68), (19, 19), (10, 25)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step108_orbit450_lb18_unconditional

theorem plane488GenSource0001 :
    QuotientRankAtLeast (spanCodes [96, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(96, 96), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0002 :
    QuotientRankAtLeast (spanCodes [96, 21, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(96, 96), (21, 20), (10, 10)]
    (codeMat 401) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0003 :
    QuotientRankAtLeast (spanCodes [96, 22, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(96, 126), (22, 30), (10, 10)]
    (codeMat 473) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0004 :
    QuotientRankAtLeast (spanCodes [96, 23, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(96, 126), (23, 30), (10, 10)]
    (codeMat 345) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane488GenSource0005 :
    QuotientRankAtLeast (spanCodes [69, 37, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(69, 129), (37, 10), (10, 20)]
    (codeMat 345) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane488GenSource0006 :
    QuotientRankAtLeast (spanCodes [70, 38, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(70, 149), (38, 30), (10, 20)]
    (codeMat 473) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane488GenSource0007 :
    QuotientRankAtLeast (spanCodes [81, 49, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(81, 129), (49, 20), (10, 10)]
    (codeMat 330) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane488GenSource0008 :
    QuotientRankAtLeast (spanCodes [83, 51, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(83, 139), (51, 30), (10, 10)]
    (codeMat 458) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane488GenSource0009 :
    QuotientRankAtLeast (spanCodes [84, 52, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [161, 20, 10] [(84, 161), (52, 30), (10, 10)]
    (codeMat 395) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane456Gen_lb18

end QiushiMatmul
