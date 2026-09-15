import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiPlane254GenFinal
import QiushiPlane269GenFinal
import QiushiPlane315GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0100 :
    QuotientRankAtLeast (spanCodes [387, 84, 34, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(387, 420), (84, 161), (34, 170), (10, 430)]
    (codeMat 351) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0101 :
    QuotientRankAtLeast (spanCodes [305, 151, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(305, 161), (151, 11), (84, 271), (10, 420)]
    (codeMat 254) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0102 :
    QuotientRankAtLeast (spanCodes [386, 84, 36, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(386, 420), (84, 271), (36, 260), (10, 430)]
    (codeMat 342) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0103 :
    QuotientRankAtLeast (spanCodes [304, 128, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(304, 261), (128, 260), (84, 171), (10, 420)]
    (codeMat 190) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0104 :
    QuotientRankAtLeast (spanCodes [400, 84, 32, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(400, 261), (84, 161), (32, 260), (10, 430)]
    (codeMat 286) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0105 :
    QuotientRankAtLeast (spanCodes [290, 148, 84, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(290, 10), (148, 11), (84, 271), (10, 420)]
    (codeMat 247) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0106 :
    QuotientRankAtLeast (spanCodes [401, 84, 39, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(401, 171), (84, 271), (39, 170), (10, 430)]
    (codeMat 279) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane487GenSource0107 :
    QuotientRankAtLeast (spanCodes [84, 8, 2, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 8, 2, 1] [(84, 84), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane254Gen_lb16

theorem plane487GenSource0108 :
    QuotientRankAtLeast (spanCodes [80, 8, 4, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(80, 264), (8, 32), (4, 2), (2, 1)]
    (codeMat 273) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane487GenSource0109 :
    QuotientRankAtLeast (spanCodes [81, 9, 5, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(81, 297), (9, 32), (5, 2), (3, 1)]
    (codeMat 281) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

end QiushiMatmul
