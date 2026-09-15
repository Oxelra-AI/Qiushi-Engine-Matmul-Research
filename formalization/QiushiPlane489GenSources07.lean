import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiPlane453GenFinal
import QiushiPlane454GenFinal
import QiushiPlane457GenFinal
import QiushiPlane458GenFinal
import QiushiPlane466GenFinal
import QiushiPlane470GenFinal
import QiushiPlane474GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0070 :
    QuotientRankAtLeast (spanCodes [258, 183, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [305, 68, 10] [(258, 315), (183, 305), (10, 383)]
    (codeMat 190) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane466Gen_lb18

theorem plane489GenSource0071 :
    QuotientRankAtLeast (spanCodes [258, 193, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 30), (193, 10), (10, 80)]
    (codeMat 204) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0072 :
    QuotientRankAtLeast (spanCodes [258, 196, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [96, 20, 10] [(258, 30), (196, 20), (10, 96)]
    (codeMat 205) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane454Gen_lb18

theorem plane489GenSource0073 :
    QuotientRankAtLeast (spanCodes [258, 198, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(258, 10), (198, 30), (10, 456)]
    (codeMat 140) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane489GenSource0074 :
    QuotientRankAtLeast (spanCodes [258, 199, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(258, 30), (199, 10), (10, 449)]
    (codeMat 225) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane489GenSource0075 :
    QuotientRankAtLeast (spanCodes [258, 208, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 10] [(258, 78), (208, 10), (10, 80)]
    (codeMat 212) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane453Gen_lb18

theorem plane489GenSource0076 :
    QuotientRankAtLeast (spanCodes [258, 211, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(258, 469), (211, 30), (10, 20)]
    (codeMat 206) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane489GenSource0077 :
    QuotientRankAtLeast (spanCodes [258, 212, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 10), (212, 94), (10, 265)]
    (codeMat 172) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0078 :
    QuotientRankAtLeast (spanCodes [258, 213, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 84, 10] [(258, 349), (213, 84), (10, 343)]
    (codeMat 486) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane470Gen_lb18

theorem plane489GenSource0079 :
    QuotientRankAtLeast (spanCodes [258, 214, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 84, 10] [(258, 10), (214, 84), (10, 300)]
    (codeMat 460) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane474Gen_lb18

end QiushiMatmul
