import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane315GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0110 :
    QuotientRankAtLeast (spanCodes [260, 128, 84, 35]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(260, 260), (128, 1), (84, 270), (35, 420)]
    (codeMat 116) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0111 :
    QuotientRankAtLeast (spanCodes [291, 163, 80, 4]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(291, 10), (163, 270), (80, 170), (4, 1)]
    (codeMat 369) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0112 :
    QuotientRankAtLeast (spanCodes [293, 161, 84, 2]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(293, 170), (161, 431), (84, 421), (2, 260)]
    (codeMat 309) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0113 :
    QuotientRankAtLeast (spanCodes [260, 139, 84, 40]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(260, 260), (139, 430), (84, 270), (40, 1)]
    (codeMat 498) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0114 :
    QuotientRankAtLeast (spanCodes [292, 163, 84, 8]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(292, 1), (163, 161), (84, 431), (8, 260)]
    (codeMat 359) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0115 :
    QuotientRankAtLeast (spanCodes [290, 163, 70, 18]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(290, 420), (163, 431), (70, 10), (18, 260)]
    (codeMat 421) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0116 :
    QuotientRankAtLeast (spanCodes [257, 149, 84, 54]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(257, 430), (149, 420), (84, 270), (54, 1)]
    (codeMat 491) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0117 :
    QuotientRankAtLeast (spanCodes [288, 163, 67, 23]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(288, 1), (163, 431), (67, 170), (23, 420)]
    (codeMat 174) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0118 :
    QuotientRankAtLeast (spanCodes [256, 155, 84, 56]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(256, 260), (155, 170), (84, 421), (56, 1)]
    (codeMat 442) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0119 :
    QuotientRankAtLeast (spanCodes [271, 148, 84, 55]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(271, 161), (148, 170), (84, 171), (55, 420)]
    (codeMat 188) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
