import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiPlane269GenFinal
import QiushiPlane276GenFinal
import QiushiStep99Orbit150Dispatch
import QiushiWcOrbit96Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0100 :
    QuotientRankAtLeast (spanCodes [260, 36, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(260, 2), (36, 1), (20, 33), (10, 297)]
    (codeMat 171) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0101 :
    QuotientRankAtLeast (spanCodes [256, 36, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(256, 2), (36, 1), (20, 33), (10, 297)]
    (codeMat 163) (codeMat 87) (codeMat 468) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0102 :
    QuotientRankAtLeast (spanCodes [288, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(288, 2), (16, 32), (10, 264), (4, 1)]
    (codeMat 177) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0103 :
    QuotientRankAtLeast (spanCodes [258, 32, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 8, 2, 1] [(258, 80), (32, 1), (16, 2), (10, 20), (4, 8)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit96_lb16_wc

theorem plane485GenSource0104 :
    QuotientRankAtLeast (spanCodes [256, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(256, 1), (64, 2), (20, 96), (10, 272)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane485GenSource0105 :
    QuotientRankAtLeast (spanCodes [260, 65, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 2, 1] [(260, 1), (65, 2), (20, 96), (10, 272)]
    (codeMat 85) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane276Gen_lb16

theorem plane485GenSource0106 :
    QuotientRankAtLeast (spanCodes [320, 17, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(320, 2), (17, 296), (10, 264), (5, 1)]
    (codeMat 225) (codeMat 468) (codeMat 87) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0107 :
    QuotientRankAtLeast (spanCodes [320, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(320, 2), (34, 296), (20, 264), (10, 297)]
    (codeMat 226) (codeMat 465) (codeMat 465) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0108 :
    QuotientRankAtLeast (spanCodes [325, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 32, 2, 1] [(325, 2), (34, 296), (20, 264), (10, 297)]
    (codeMat 234) (codeMat 465) (codeMat 465) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane269Gen_lb16

theorem plane485GenSource0109 :
    QuotientRankAtLeast (spanCodes [262, 65, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(262, 264), (65, 16), (32, 1), (20, 68), (10, 258)]
    (codeMat 106) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

end QiushiMatmul
