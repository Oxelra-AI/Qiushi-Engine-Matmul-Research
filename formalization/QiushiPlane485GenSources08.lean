import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane295GenFinal
import QiushiPlane419GenFinal
import QiushiPlane427GenFinal
import QiushiPlane457GenFinal
import QiushiPlane458GenFinal
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0080 :
    QuotientRankAtLeast (spanCodes [480, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(480, 449), (20, 10), (10, 20)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane485GenSource0081 :
    QuotientRankAtLeast (spanCodes [482, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(482, 470), (20, 20), (10, 30)]
    (codeMat 275) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0082 :
    QuotientRankAtLeast (spanCodes [483, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(483, 456), (20, 10), (10, 30)]
    (codeMat 346) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0083 :
    QuotientRankAtLeast (spanCodes [484, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(484, 456), (20, 10), (10, 30)]
    (codeMat 282) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0084 :
    QuotientRankAtLeast (spanCodes [485, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [450, 20, 10] [(485, 470), (20, 20), (10, 30)]
    (codeMat 339) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane458Gen_lb18

theorem plane485GenSource0085 :
    QuotientRankAtLeast (spanCodes [487, 20, 10]) 18 := by
  apply quotientRankAtLeast_weaken (n := 18) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [449, 20, 10] [(487, 469), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane457Gen_lb18

theorem plane485GenSource0086 :
    QuotientRankAtLeast (spanCodes [20, 9, 3]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(20, 43), (9, 32), (3, 1)]
    (codeMat 281) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane485GenSource0087 :
    QuotientRankAtLeast (spanCodes [18, 10, 6]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [36, 16, 1] [(18, 36), (10, 37), (6, 16)]
    (codeMat 266) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane427Gen_lb17

theorem plane485GenSource0088 :
    QuotientRankAtLeast (spanCodes [36, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 10, 1] [(36, 32), (20, 33), (10, 43)]
    (codeMat 282) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane419Gen_lb17

theorem plane485GenSource0089 :
    QuotientRankAtLeast (spanCodes [322, 34, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 32, 10, 1] [(322, 283), (34, 11), (20, 10), (10, 43)]
    (codeMat 275) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane295Gen_lb17

end QiushiMatmul
