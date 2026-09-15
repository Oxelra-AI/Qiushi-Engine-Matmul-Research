import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit144Dispatch
import QiushiStep99Orbit231Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource0480 :
    QuotientRankAtLeast (spanCodes [256, 134, 103, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 140, 98, 16, 1] [(256, 256), (134, 272), (103, 396), (19, 238), (10, 371)]
    (codeMat 302) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit231_lb15_unconditional

theorem plane484GenSource0481 :
    QuotientRankAtLeast (spanCodes [260, 131, 102, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (131, 440), (102, 492), (19, 441), (10, 462)]
    (codeMat 302) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0482 :
    QuotientRankAtLeast (spanCodes [260, 164, 65, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 3), (164, 411), (65, 1), (19, 119), (10, 462)]
    (codeMat 309) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0483 :
    QuotientRankAtLeast (spanCodes [256, 161, 64, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 2), (161, 84), (64, 1), (19, 441), (10, 462)]
    (codeMat 372) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0484 :
    QuotientRankAtLeast (spanCodes [292, 134, 67, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 2), (134, 493), (67, 118), (19, 462), (10, 119)]
    (codeMat 311) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0485 :
    QuotientRankAtLeast (spanCodes [258, 161, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(258, 408), (161, 85), (66, 440), (19, 462), (10, 441)]
    (codeMat 358) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0486 :
    QuotientRankAtLeast (spanCodes [256, 163, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(256, 32), (163, 492), (66, 440), (19, 462), (10, 441)]
    (codeMat 358) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0487 :
    QuotientRankAtLeast (spanCodes [263, 164, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(263, 408), (164, 493), (66, 440), (19, 119), (10, 441)]
    (codeMat 302) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0488 :
    QuotientRankAtLeast (spanCodes [260, 167, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(260, 32), (167, 84), (66, 440), (19, 119), (10, 441)]
    (codeMat 302) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane484GenSource0489 :
    QuotientRankAtLeast (spanCodes [292, 135, 66, 19, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(292, 32), (135, 411), (66, 118), (19, 441), (10, 119)]
    (codeMat 318) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

end QiushiMatmul
