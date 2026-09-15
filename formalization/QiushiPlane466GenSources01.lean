import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiStep132Mono385From243
import QiushiStep133Mono397From243
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0010 :
    QuotientRankAtLeast (spanCodes [305, 160, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(305, 250), (160, 68), (68, 170), (10, 228)]
    (codeMat 174) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane466GenSource0011 :
    QuotientRankAtLeast (spanCodes [305, 180, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(305, 116), (180, 237), (68, 147), (10, 135)]
    (codeMat 460) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane466GenSource0012 :
    QuotientRankAtLeast (spanCodes [305, 182, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(305, 116), (182, 126), (68, 20), (10, 135)]
    (codeMat 169) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane466GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 68, 36, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 393), (68, 301), (36, 1), (23, 263), (10, 133)]
    (codeMat 115) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane466GenSource0014 :
    QuotientRankAtLeast (spanCodes [261, 68, 35, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(261, 38), (68, 50), (35, 175), (23, 509), (10, 186)]
    (codeMat 270) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane466GenSource0015 :
    QuotientRankAtLeast (spanCodes [261, 68, 36, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(261, 310), (68, 164), (36, 32), (16, 1), (10, 11)]
    (codeMat 282) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane466GenSource0016 :
    QuotientRankAtLeast (spanCodes [263, 68, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(263, 175), (68, 418), (34, 11), (20, 10), (10, 43)]
    (codeMat 403) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane466GenSource0017 :
    QuotientRankAtLeast (spanCodes [263, 68, 37, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(263, 373), (68, 186), (37, 21), (19, 20), (10, 50)]
    (codeMat 395) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane466GenSource0018 :
    QuotientRankAtLeast (spanCodes [290, 129, 68, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 33), (129, 278), (68, 175), (19, 310), (10, 164)]
    (codeMat 190) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane466GenSource0019 :
    QuotientRankAtLeast (spanCodes [295, 132, 68, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(295, 262), (132, 392), (68, 424), (22, 393), (10, 301)]
    (codeMat 103) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

end QiushiMatmul
