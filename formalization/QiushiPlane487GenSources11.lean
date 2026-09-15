import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane269GenFinal
import QiushiPlane292GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0110 :
    QuotientRankAtLeast (spanCodes [80, 9, 4, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(80, 297), (9, 32), (4, 2), (3, 1)]
    (codeMat 345) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane487GenSource0111 :
    QuotientRankAtLeast (spanCodes [81, 8, 5, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(81, 264), (8, 32), (5, 2), (2, 1)]
    (codeMat 337) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane487GenSource0112 :
    QuotientRankAtLeast (spanCodes [64, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(64, 128), (16, 1), (10, 10), (4, 32)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0113 :
    QuotientRankAtLeast (spanCodes [64, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(64, 128), (17, 11), (10, 10), (5, 32)]
    (codeMat 267) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0114 :
    QuotientRankAtLeast (spanCodes [65, 16, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(65, 128), (16, 1), (10, 10), (5, 32)]
    (codeMat 330) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0115 :
    QuotientRankAtLeast (spanCodes [65, 17, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(65, 128), (17, 11), (10, 10), (4, 32)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0116 :
    QuotientRankAtLeast (spanCodes [66, 16, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(66, 138), (16, 1), (10, 10), (6, 32)]
    (codeMat 394) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0117 :
    QuotientRankAtLeast (spanCodes [66, 17, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 10, 1] [(66, 138), (17, 11), (10, 10), (7, 32)]
    (codeMat 395) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane292Gen_lb16

theorem plane487GenSource0118 :
    QuotientRankAtLeast (spanCodes [64, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(64, 2), (20, 264), (8, 1), (2, 32)]
    (codeMat 98) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane487GenSource0119 :
    QuotientRankAtLeast (spanCodes [65, 21, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(65, 2), (21, 297), (9, 1), (3, 32)]
    (codeMat 107) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

end QiushiMatmul
