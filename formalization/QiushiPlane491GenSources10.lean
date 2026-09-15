import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane315GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0100 :
    QuotientRankAtLeast (spanCodes [144, 84, 51, 12]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(144, 1), (84, 421), (51, 170), (12, 430)]
    (codeMat 342) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0101 :
    QuotientRankAtLeast (spanCodes [257, 163, 84, 9]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(257, 160), (163, 270), (84, 171), (9, 260)]
    (codeMat 303) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0102 :
    QuotientRankAtLeast (spanCodes [272, 160, 84, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(272, 11), (160, 10), (84, 161), (3, 260)]
    (codeMat 486) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0103 :
    QuotientRankAtLeast (spanCodes [257, 163, 64, 20]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(257, 11), (163, 171), (64, 1), (20, 420)]
    (codeMat 236) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0104 :
    QuotientRankAtLeast (spanCodes [272, 163, 81, 5]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(272, 420), (163, 161), (81, 430), (5, 1)]
    (codeMat 425) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0105 :
    QuotientRankAtLeast (spanCodes [271, 142, 84, 45]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(271, 171), (142, 271), (84, 161), (45, 1)]
    (codeMat 379) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0106 :
    QuotientRankAtLeast (spanCodes [273, 144, 84, 51]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(273, 171), (144, 1), (84, 431), (51, 160)]
    (codeMat 206) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0107 :
    QuotientRankAtLeast (spanCodes [264, 136, 84, 43]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(264, 430), (136, 170), (84, 161), (43, 420)]
    (codeMat 247) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0108 :
    QuotientRankAtLeast (spanCodes [273, 150, 84, 53]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(273, 161), (150, 11), (84, 421), (53, 160)]
    (codeMat 143) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0109 :
    QuotientRankAtLeast (spanCodes [256, 134, 84, 37]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(256, 260), (134, 261), (84, 431), (37, 420)]
    (codeMat 125) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
