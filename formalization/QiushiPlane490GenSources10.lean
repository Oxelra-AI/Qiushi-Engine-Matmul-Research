import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane295GenFinal
import QiushiPlane315GenFinal
import QiushiPlane447GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0100 :
    QuotientRankAtLeast (spanCodes [275, 70, 50, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 421), (70, 160), (50, 430), (10, 170)]
    (codeMat 335) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0101 :
    QuotientRankAtLeast (spanCodes [275, 147, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [306, 160, 1] [(275, 403), (147, 402), (10, 160)]
    (codeMat 84) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane447Gen_lb17

theorem plane490GenSource0102 :
    QuotientRankAtLeast (spanCodes [275, 162, 10, 7]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 271), (162, 10), (10, 170), (7, 260)]
    (codeMat 407) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0103 :
    QuotientRankAtLeast (spanCodes [275, 149, 39, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 421), (149, 420), (39, 430), (10, 170)]
    (codeMat 405) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0104 :
    QuotientRankAtLeast (spanCodes [275, 129, 65, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 282), (129, 33), (65, 1), (10, 43)]
    (codeMat 309) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0105 :
    QuotientRankAtLeast (spanCodes [275, 144, 80, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 305), (144, 1), (80, 33), (10, 43)]
    (codeMat 302) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0106 :
    QuotientRankAtLeast (spanCodes [275, 128, 65, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 305), (128, 32), (65, 1), (10, 43)]
    (codeMat 317) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0107 :
    QuotientRankAtLeast (spanCodes [275, 178, 113, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(275, 271), (178, 170), (113, 430), (10, 160)]
    (codeMat 214) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane490GenSource0108 :
    QuotientRankAtLeast (spanCodes [275, 144, 64, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 282), (144, 1), (64, 32), (10, 43)]
    (codeMat 318) (codeMat 270) (codeMat 298) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane490GenSource0109 :
    QuotientRankAtLeast (spanCodes [275, 128, 81, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(275, 282), (128, 32), (81, 10), (10, 43)]
    (codeMat 303) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

end QiushiMatmul
