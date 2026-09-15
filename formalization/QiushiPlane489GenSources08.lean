import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane454GenFinal
import QiushiPlane458GenFinal
import QiushiPlane464GenFinal
import QiushiPlane466GenFinal
import QiushiPlane470GenFinal
import QiushiPlane471GenFinal
import QiushiPlane474GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0080 :
    QuotientRankAtLeast (spanCodes [258, 215, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(258, 373), (215, 305), (10, 383)]
    (codeMat 230) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane489GenSource0081 :
    QuotientRankAtLeast (spanCodes [258, 224, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 126), (224, 20), (10, 96)]
    (codeMat 214) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0082 :
    QuotientRankAtLeast (spanCodes [258, 225, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 259), (225, 94), (10, 265)]
    (codeMat 116) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0083 :
    QuotientRankAtLeast (spanCodes [258, 226, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 450), (226, 470), (10, 456)]
    (codeMat 84) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0084 :
    QuotientRankAtLeast (spanCodes [258, 227, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(258, 294), (227, 376), (10, 300)]
    (codeMat 468) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

theorem plane489GenSource0085 :
    QuotientRankAtLeast (spanCodes [258, 228, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [180, 68, 10] [(258, 240), (228, 78), (10, 68)]
    (codeMat 107) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane464Gen_lb18

theorem plane489GenSource0086 :
    QuotientRankAtLeast (spanCodes [258, 229, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 349), (229, 84), (10, 10)]
    (codeMat 459) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0087 :
    QuotientRankAtLeast (spanCodes [258, 230, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [289, 84, 10] [(258, 383), (230, 94), (10, 10)]
    (codeMat 339) (codeMat 285) (codeMat 317) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane471Gen_lb18

theorem plane489GenSource0088 :
    QuotientRankAtLeast (spanCodes [258, 231, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(258, 383), (231, 78), (10, 68)]
    (codeMat 123) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane489GenSource0089 :
    QuotientRankAtLeast (spanCodes [258, 241, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 10), (241, 84), (10, 343)]
    (codeMat 485) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

end QiushiMatmul
