import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit231Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0720 :
    QuotientRankAtLeast (spanCodes [263, 129, 96, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(263, 408), (129, 440), (96, 493), (19, 441), (10, 119)]
    (codeMat 303) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0721 :
    QuotientRankAtLeast (spanCodes [292, 163, 97, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 2), (163, 410), (97, 34), (19, 119), (10, 462)]
    (codeMat 303) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0722 :
    QuotientRankAtLeast (spanCodes [292, 132, 70, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 3), (132, 411), (70, 493), (19, 441), (10, 462)]
    (codeMat 311) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0723 :
    QuotientRankAtLeast (spanCodes [288, 129, 71, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 32), (129, 118), (71, 411), (19, 119), (10, 441)]
    (codeMat 311) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0724 :
    QuotientRankAtLeast (spanCodes [256, 163, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(256, 256), (163, 156), (69, 272), (19, 413), (10, 238)]
    (codeMat 302) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane484GenSource0725 :
    QuotientRankAtLeast (spanCodes [292, 135, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 2), (135, 411), (69, 493), (19, 441), (10, 462)]
    (codeMat 311) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0726 :
    QuotientRankAtLeast (spanCodes [295, 132, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(295, 33), (132, 493), (69, 411), (19, 462), (10, 441)]
    (codeMat 318) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0727 :
    QuotientRankAtLeast (spanCodes [288, 131, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 2), (131, 118), (69, 493), (19, 119), (10, 462)]
    (codeMat 318) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0728 :
    QuotientRankAtLeast (spanCodes [290, 129, 69, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(290, 33), (129, 118), (69, 411), (19, 119), (10, 441)]
    (codeMat 311) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0729 :
    QuotientRankAtLeast (spanCodes [288, 132, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(288, 3), (132, 411), (66, 118), (19, 441), (10, 119)]
    (codeMat 318) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
