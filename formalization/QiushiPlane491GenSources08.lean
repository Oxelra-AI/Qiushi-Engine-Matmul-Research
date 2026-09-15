import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiPlane315GenFinal
import QiushiPlane449GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0080 :
    QuotientRankAtLeast (spanCodes [163, 68, 16, 9]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(163, 270), (68, 160), (16, 1), (9, 260)]
    (codeMat 106) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0081 :
    QuotientRankAtLeast (spanCodes [162, 76, 24, 1]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(162, 430), (76, 10), (24, 260), (1, 1)]
    (codeMat 249) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0082 :
    QuotientRankAtLeast (spanCodes [163, 71, 19, 8]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(163, 171), (71, 160), (19, 261), (8, 260)]
    (codeMat 99) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0083 :
    QuotientRankAtLeast (spanCodes [161, 77, 25, 2]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(161, 421), (77, 170), (25, 261), (2, 260)]
    (codeMat 179) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0084 :
    QuotientRankAtLeast (spanCodes [135, 84, 36]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [316, 160, 1] [(135, 160), (84, 412), (36, 1)]
    (codeMat 107) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane449Gen_lb17

theorem plane491GenSource0085 :
    QuotientRankAtLeast (spanCodes [130, 80, 33, 4]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(130, 260), (80, 160), (33, 10), (4, 1)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0086 :
    QuotientRankAtLeast (spanCodes [128, 82, 35, 6]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(128, 1), (82, 10), (35, 430), (6, 260)]
    (codeMat 348) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0087 :
    QuotientRankAtLeast (spanCodes [137, 82, 42, 6]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(137, 11), (82, 10), (42, 430), (6, 260)]
    (codeMat 415) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0088 :
    QuotientRankAtLeast (spanCodes [130, 84, 33, 12]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(130, 260), (84, 171), (33, 10), (12, 11)]
    (codeMat 403) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane491GenSource0089 :
    QuotientRankAtLeast (spanCodes [137, 81, 42, 5]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(137, 160), (81, 420), (42, 11), (5, 1)]
    (codeMat 473) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
