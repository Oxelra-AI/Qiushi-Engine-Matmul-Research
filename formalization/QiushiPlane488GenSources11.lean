import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane255GenFinal
import QiushiPlane269GenFinal
import QiushiPlane292GenFinal
import QiushiPlane315GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0110 :
    QuotientRankAtLeast (spanCodes [390, 71, 39, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(390, 1), (71, 10), (39, 430), (10, 170)]
    (codeMat 397) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane488GenSource0111 :
    QuotientRankAtLeast (spanCodes [417, 96, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(417, 270), (96, 170), (17, 10), (10, 11)]
    (codeMat 339) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane488GenSource0112 :
    QuotientRankAtLeast (spanCodes [405, 68, 36, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(405, 271), (68, 160), (36, 260), (10, 170)]
    (codeMat 271) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane488GenSource0113 :
    QuotientRankAtLeast (spanCodes [96, 8, 4, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(96, 264), (8, 32), (4, 1), (2, 2)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane488GenSource0114 :
    QuotientRankAtLeast (spanCodes [96, 9, 5, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(96, 297), (9, 32), (5, 1), (3, 2)]
    (codeMat 345) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane488GenSource0115 :
    QuotientRankAtLeast (spanCodes [96, 9, 4, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(96, 265), (9, 32), (4, 1), (3, 2)]
    (codeMat 281) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane488GenSource0116 :
    QuotientRankAtLeast (spanCodes [96, 8, 5, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(96, 296), (8, 32), (5, 1), (2, 2)]
    (codeMat 273) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane488GenSource0117 :
    QuotientRankAtLeast (spanCodes [96, 16, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 8, 2, 1] [(96, 96), (16, 1), (8, 8), (2, 2)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane255Gen_lb16

theorem plane488GenSource0118 :
    QuotientRankAtLeast (spanCodes [67, 35, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(67, 170), (35, 33), (10, 42), (7, 32)]
    (codeMat 459) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane488GenSource0119 :
    QuotientRankAtLeast (spanCodes [65, 33, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(65, 128), (33, 11), (10, 42), (6, 32)]
    (codeMat 331) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

end QiushiMatmul
