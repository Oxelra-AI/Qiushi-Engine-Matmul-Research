import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiPlane282GenFinal
import QiushiPlane295GenFinal
import QiushiPlane315GenFinal
import QiushiPlane434GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0100 :
    QuotientRankAtLeast (spanCodes [288, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [266, 16, 1] [(288, 1), (96, 17), (10, 283)]
    (codeMat 102) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane434Gen_lb17

theorem plane488GenSource0101 :
    QuotientRankAtLeast (spanCodes [256, 66, 34, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(256, 1), (66, 259), (34, 264), (10, 280)]
    (codeMat 84) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane488GenSource0102 :
    QuotientRankAtLeast (spanCodes [258, 64, 32, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 16, 10, 1] [(258, 258), (64, 1), (32, 16), (10, 264)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane282Gen_lb17

theorem plane488GenSource0103 :
    QuotientRankAtLeast (spanCodes [292, 96, 17, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(292, 260), (96, 160), (17, 10), (10, 11)]
    (codeMat 275) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane488GenSource0104 :
    QuotientRankAtLeast (spanCodes [272, 144, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(272, 33), (144, 32), (96, 42), (10, 283)]
    (codeMat 244) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0105 :
    QuotientRankAtLeast (spanCodes [308, 178, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(308, 11), (178, 10), (96, 430), (10, 160)]
    (codeMat 213) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

theorem plane488GenSource0106 :
    QuotientRankAtLeast (spanCodes [384, 96, 16, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(384, 1), (96, 42), (16, 32), (10, 272)]
    (codeMat 84) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0107 :
    QuotientRankAtLeast (spanCodes [274, 128, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(274, 272), (128, 32), (96, 42), (10, 283)]
    (codeMat 230) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0108 :
    QuotientRankAtLeast (spanCodes [386, 96, 16, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(386, 283), (96, 42), (16, 32), (10, 272)]
    (codeMat 86) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

theorem plane488GenSource0109 :
    QuotientRankAtLeast (spanCodes [309, 160, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 10, 1] [(309, 421), (160, 170), (96, 430), (10, 160)]
    (codeMat 215) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane315Gen_lb17

end QiushiMatmul
