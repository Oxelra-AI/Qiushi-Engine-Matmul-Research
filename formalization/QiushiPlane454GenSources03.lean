import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit216Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0030 :
    QuotientRankAtLeast (spanCodes [261, 131, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(261, 284), (131, 228), (96, 97), (20, 238), (10, 374)]
    (codeMat 318) (codeMat 351) (codeMat 239) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane454GenSource0031 :
    QuotientRankAtLeast (spanCodes [288, 167, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(288, 504), (167, 409), (96, 505), (20, 278), (10, 402)]
    (codeMat 92) (codeMat 379) (codeMat 247) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane454GenSource0032 :
    QuotientRankAtLeast (spanCodes [289, 166, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(289, 97), (166, 137), (96, 463), (20, 338), (10, 21)]
    (codeMat 478) (codeMat 318) (codeMat 299) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane454GenSource0033 :
    QuotientRankAtLeast (spanCodes [386, 96, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(386, 373), (96, 164), (17, 11), (10, 10), (5, 32)]
    (codeMat 395) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane454GenSource0034 :
    QuotientRankAtLeast (spanCodes [388, 96, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(388, 276), (96, 363), (20, 97), (9, 1), (3, 256)]
    (codeMat 107) (codeMat 423) (codeMat 181) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane454GenSource0035 :
    QuotientRankAtLeast (spanCodes [389, 96, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(389, 133), (96, 284), (20, 11), (8, 32), (2, 1)]
    (codeMat 337) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane454GenSource0036 :
    QuotientRankAtLeast (spanCodes [262, 166, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(262, 506), (166, 464), (96, 43), (20, 383), (10, 164)]
    (codeMat 244) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane454GenSource0037 :
    QuotientRankAtLeast (spanCodes [263, 167, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(263, 11), (167, 143), (96, 133), (20, 402), (10, 374)]
    (codeMat 172) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane454GenSource0038 :
    QuotientRankAtLeast (spanCodes [391, 70, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(391, 300), (70, 97), (38, 327), (20, 133), (10, 451)]
    (codeMat 234) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

theorem plane454GenSource0039 :
    QuotientRankAtLeast (spanCodes [416, 96, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(416, 383), (96, 127), (20, 21), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

end QiushiMatmul
