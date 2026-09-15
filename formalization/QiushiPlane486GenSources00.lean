import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiPlane453GenFinal
import QiushiPlane455GenFinal
import QiushiStep108Orbit450Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0000 :
    QuotientRankAtLeast (spanCodes [68, 19, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 19, 10] [(68, 68), (19, 19), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step108_orbit450_lb18_unconditional

theorem plane486GenSource0001 :
    QuotientRankAtLeast (spanCodes [68, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(68, 68), (20, 20), (10, 10)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0002 :
    QuotientRankAtLeast (spanCodes [68, 21, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(68, 68), (21, 30), (10, 10)]
    (codeMat 281) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0003 :
    QuotientRankAtLeast (spanCodes [68, 22, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(68, 78), (22, 20), (10, 10)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0004 :
    QuotientRankAtLeast (spanCodes [68, 23, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(68, 78), (23, 30), (10, 10)]
    (codeMat 409) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane486GenSource0005 :
    QuotientRankAtLeast (spanCodes [68, 33, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(68, 129), (33, 10), (10, 20)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0006 :
    QuotientRankAtLeast (spanCodes [68, 35, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(68, 129), (35, 30), (10, 20)]
    (codeMat 337) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0007 :
    QuotientRankAtLeast (spanCodes [68, 37, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(68, 129), (37, 10), (10, 20)]
    (codeMat 281) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0008 :
    QuotientRankAtLeast (spanCodes [68, 38, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(68, 129), (38, 30), (10, 20)]
    (codeMat 345) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

theorem plane486GenSource0009 :
    QuotientRankAtLeast (spanCodes [68, 49, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [129, 20, 10] [(68, 149), (49, 10), (10, 20)]
    (codeMat 401) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane455Gen_lb18

end QiushiMatmul
