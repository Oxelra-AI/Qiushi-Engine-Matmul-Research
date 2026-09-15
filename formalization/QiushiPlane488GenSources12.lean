import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane269GenFinal
import QiushiPlane274GenFinal
import QiushiPlane292GenFinal
import QiushiWcOrbit264Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0120 :
    QuotientRankAtLeast (spanCodes [80, 48, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(80, 12), (48, 2), (8, 1), (2, 256)]
    (codeMat 98) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane488GenSource0121 :
    QuotientRankAtLeast (spanCodes [85, 53, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(85, 85), (53, 35), (9, 1), (3, 32)]
    (codeMat 267) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane488GenSource0122 :
    QuotientRankAtLeast (spanCodes [128, 96, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(128, 1), (96, 264), (8, 32), (2, 2)]
    (codeMat 140) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane488GenSource0123 :
    QuotientRankAtLeast (spanCodes [130, 96, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(130, 3), (96, 297), (18, 2), (10, 34)]
    (codeMat 158) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane488GenSource0124 :
    QuotientRankAtLeast (spanCodes [128, 96, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(128, 1), (96, 265), (18, 2), (10, 34)]
    (codeMat 156) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane488GenSource0125 :
    QuotientRankAtLeast (spanCodes [146, 82, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(146, 128), (82, 129), (50, 170), (10, 138)]
    (codeMat 468) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane488GenSource0126 :
    QuotientRankAtLeast (spanCodes [146, 67, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 2, 1] [(146, 1), (67, 82), (35, 240), (10, 80)]
    (codeMat 87) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274Gen_lb16

theorem plane488GenSource0127 :
    QuotientRankAtLeast (spanCodes [163, 96, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(163, 117), (96, 119), (18, 32), (10, 33)]
    (codeMat 234) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane488GenSource0128 :
    QuotientRankAtLeast (spanCodes [130, 80, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(130, 128), (80, 11), (48, 32), (10, 138)]
    (codeMat 342) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane488GenSource0129 :
    QuotientRankAtLeast (spanCodes [288, 96, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(288, 2), (96, 34), (10, 118), (4, 1)]
    (codeMat 305) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

end QiushiMatmul
