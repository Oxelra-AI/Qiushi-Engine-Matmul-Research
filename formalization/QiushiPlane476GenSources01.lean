import QiushiPlane476GenData
import QiushiCertifiedTransport
import QiushiStep107Orbit373Extraction
import QiushiStep133Mono397From243
import QiushiStep133Mono409From247T
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane476GenSource0010 :
    QuotientRankAtLeast (spanCodes [276, 165, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 165, 96, 10] [(276, 10), (165, 465), (96, 276), (10, 96)]
    (codeMat 85) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit409_lb17_mono

theorem plane476GenSource0011 :
    QuotientRankAtLeast (spanCodes [276, 176, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(276, 30), (176, 10), (96, 147), (10, 231)]
    (codeMat 230) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane476GenSource0012 :
    QuotientRankAtLeast (spanCodes [276, 178, 96, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [300, 224, 20, 1] [(276, 472), (178, 312), (96, 21), (10, 300)]
    (codeMat 470) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step107_orbit373_lb17

theorem plane476GenSource0013 :
    QuotientRankAtLeast (spanCodes [274, 83, 51, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(274, 496), (83, 373), (51, 10), (10, 43), (6, 1)]
    (codeMat 281) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane476GenSource0014 :
    QuotientRankAtLeast (spanCodes [259, 64, 32, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 440), (64, 1), (32, 32), (23, 164), (10, 434)]
    (codeMat 156) (codeMat 179) (codeMat 421) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane476GenSource0015 :
    QuotientRankAtLeast (spanCodes [275, 128, 96, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(275, 239), (128, 504), (96, 381), (10, 96), (7, 1)]
    (codeMat 241) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane476GenSource0016 :
    QuotientRankAtLeast (spanCodes [276, 133, 96, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(276, 96), (133, 10), (96, 350), (8, 432), (2, 1)]
    (codeMat 489) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane476GenSource0017 :
    QuotientRankAtLeast (spanCodes [262, 131, 96, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 287), (131, 353), (96, 363), (18, 256), (10, 257)]
    (codeMat 250) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane476GenSource0018 :
    QuotientRankAtLeast (spanCodes [259, 133, 96, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 132), (133, 133), (96, 374), (23, 381), (10, 284)]
    (codeMat 285) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane476GenSource0019 :
    QuotientRankAtLeast (spanCodes [260, 133, 96, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(260, 504), (133, 133), (96, 96), (16, 1), (10, 10)]
    (codeMat 394) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
