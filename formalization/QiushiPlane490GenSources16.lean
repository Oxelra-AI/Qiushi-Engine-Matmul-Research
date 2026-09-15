import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane274GenFinal
import QiushiPlane276GenFinal
import QiushiPlane298GenFinal
import QiushiStep99Orbit150Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0160 :
    QuotientRankAtLeast (spanCodes [260, 135, 33, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(260, 16), (135, 280), (33, 258), (23, 259), (10, 326)]
    (codeMat 107) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0161 :
    QuotientRankAtLeast (spanCodes [275, 144, 83, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 417), (144, 32), (83, 33), (10, 42)]
    (codeMat 405) (codeMat 317) (codeMat 285) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0162 :
    QuotientRankAtLeast (spanCodes [272, 192, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(272, 118), (192, 1), (9, 32), (3, 2)]
    (codeMat 204) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0163 :
    QuotientRankAtLeast (spanCodes [275, 147, 80, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(275, 342), (147, 333), (80, 332), (10, 264), (5, 16)]
    (codeMat 205) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane490GenSource0164 :
    QuotientRankAtLeast (spanCodes [275, 130, 83, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 395), (130, 1), (83, 11), (10, 42)]
    (codeMat 477) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0165 :
    QuotientRankAtLeast (spanCodes [275, 147, 66, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 417), (147, 33), (66, 43), (10, 42)]
    (codeMat 478) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0166 :
    QuotientRankAtLeast (spanCodes [275, 165, 116, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(275, 369), (165, 370), (116, 98), (10, 274)]
    (codeMat 239) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane490GenSource0167 :
    QuotientRankAtLeast (spanCodes [275, 144, 66, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 80, 2, 1] [(275, 241), (144, 1), (66, 80), (10, 82)]
    (codeMat 102) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane274Gen_lb16

theorem plane490GenSource0168 :
    QuotientRankAtLeast (spanCodes [275, 147, 65, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 395), (147, 11), (65, 32), (10, 42)]
    (codeMat 334) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0169 :
    QuotientRankAtLeast (spanCodes [257, 192, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(257, 118), (192, 1), (18, 32), (10, 34)]
    (codeMat 212) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

end QiushiMatmul
