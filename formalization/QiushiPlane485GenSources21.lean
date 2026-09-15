import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit65Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0210 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 22), (68, 148), (32, 3), (20, 31), (10, 252)]
    (codeMat 102) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0211 :
    QuotientRankAtLeast (spanCodes [257, 135, 68, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (135, 149), (68, 150), (34, 104), (20, 96), (10, 232)]
    (codeMat 157) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0212 :
    QuotientRankAtLeast (spanCodes [259, 132, 64, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(259, 176), (132, 480), (64, 320), (39, 436), (20, 507), (10, 437)]
    (codeMat 299) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0213 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 148), (130, 128), (68, 150), (39, 252), (20, 224), (10, 255)]
    (codeMat 110) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0214 :
    QuotientRankAtLeast (spanCodes [260, 196, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (196, 34), (33, 440), (20, 463), (10, 118)]
    (codeMat 355) (codeMat 242) (codeMat 205) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane485GenSource0215 :
    QuotientRankAtLeast (spanCodes [385, 65, 33, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(385, 34), (65, 32), (33, 463), (20, 118), (10, 440)]
    (codeMat 355) (codeMat 428) (codeMat 107) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane485GenSource0216 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (131, 336), (64, 16), (32, 1), (20, 79), (10, 506)]
    (codeMat 354) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0217 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 496), (129, 160), (66, 176), (32, 1), (20, 78), (10, 436)]
    (codeMat 298) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane485GenSource0218 :
    QuotientRankAtLeast (spanCodes [260, 130, 71, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 1), (130, 9), (71, 104), (32, 3), (20, 31), (10, 252)]
    (codeMat 125) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane485GenSource0219 :
    QuotientRankAtLeast (spanCodes [258, 129, 64, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 436), (129, 78), (64, 1), (34, 176), (20, 160), (10, 496)]
    (codeMat 156) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
